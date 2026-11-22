-- Prove2me | solution 1 for ShiTM.piecewise_layout_block_residual_stack_lengths_are_exact
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-18T08:21:47.626821+00:00
-- url     : https://prove2.me/submissions/a4324d60-be27-4b77-b163-5abfe13a41c1

/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import Mathlib.Computability.TuringMachine.Computable
import Theorems.Thm_ShiTM_copy_loop_transfers_stack
import Theorems.Thm_ShiTM_branch_loop_transfers_prefix_until_symbol

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open Turing Turing.TM2

/-!
# The RESIDUAL PIECE-STACK HEIGHTS of the many-piece layout dispatch

`ShiTM.piecewise_layout_index_block_and_amplifier_instantiation` runs the thirteen-piece
piecewise-affine wire map as one `Turing.TM2` block: six pairwise-distinct stacks, the piece
list carried as DATA on the length stack `kl` (`replicate a ml ++ dl :: ...`) and the base
stack `kb` (`replicate b mb ++ db :: ...`), the remaining index as marks on `kv`, a per-piece
bank on `kd`, the output on `ku` and a discard stack `kr`.  It reports the computed index
`D ps w`, the step count `C ps w` -- and, for the two piece stacks it has EATEN, only the
inequalities

    (T kl).length <= (S kl).length      (T kb).length <= (S kb).length

with the popped material pushed to `kr` and forgotten.

## Why bounds are not enough

Composing the block with a downstream pass that RELOADS the piece stacks makes the total cost
depend on those two residual heights.  With bounds only, the composite has to witness them
existentially, and an existentially witnessed cost cannot be fed to an iteration principle
that demands an EXACT iterate equation -- only to one that demands a bound.  But the residual
heights are not free: they are determined by `(ps, w)`, because the walk's descent is
deterministic and destroys a known amount of each stack per piece.

## The two recursions

On the FOUND piece `(a, b)` -- the first with `w < a` -- the walk has popped `w` marks and
peeked the `(w+1)`-st, so `kl` retains `a - w - 1` marks and that piece's delimiter, then the
whole of `PL t`; and `lf` drains exactly that piece's base block, so `kb` retains `PB t`.  On
an ADVANCE piece both blocks are consumed whole and the walk recurses at `(t, w - a)`.  Since
the packing gives `(PL t).length = sum over t of (len + 1)` above `PL []`, the two heights are

    R1 ((a, b) :: t) w = if w < a then (a - w) + sum over t of (len  + 1) else R1 t (w - a)
    R2 ((a, b) :: t) w = if w < a then           sum over t of (base + 1) else R2 t (w - a)

-- the SAME relative-offset descent as `D` and `C`, on the same piece list, so the composite's
cost becomes a function of the element and the fixed piece list alone.  Both are bounded by
the stacks' own heights, so the original inequalities are recovered.

The walk is re-proved here rather than cited: the residual heights are existentially
quantified inside the accepted statement's conclusion, so no amount of post-processing of that
statement can pin them, and the induction over the piece list has to be redone carrying the
two length equations.  The four drain phases are still the accepted shapes
`ShiTM.copy_loop_transfers_stack` and `ShiTM.branch_loop_transfers_prefix_until_symbol`, cited
and not re-proved; only the fused comparison node `l1` is proved from the one-`stepAux`-node
lemmas.
-/

/-! ### Self-contained `List.replicate` facts -/
private theorem shiRl_len_repl {al : Type} (n : ℕ) (x : al) :
    (List.replicate n x).length = n := by
  simp

private theorem shiRl_map_rev {al bl : Type} (n : ℕ) (x : al) (e : al → bl) :
    ((List.replicate n x).map e).reverse = List.replicate n (e x) := by
  simp

private theorem shiRl_repl_snoc {al : Type} (x : al) (l : List al) : ∀ n : ℕ,
    List.replicate (n + 1) x ++ l = List.replicate n x ++ x :: l := by
  intro n
  induction n with
  | zero => rfl
  | succ p ih =>
    have h1 : List.replicate (p + 1 + 1) x ++ l
        = x :: (List.replicate (p + 1) x ++ l) := rfl
    have h2 : List.replicate (p + 1) x ++ x :: l
        = x :: (List.replicate p x ++ x :: l) := rfl
    rw [h1, h2, ih]

private theorem shiRl_repl_join {al : Type} (b : ℕ) (x : al) (l : List al) : ∀ a : ℕ,
    List.replicate a x ++ (List.replicate b x ++ l) = List.replicate (b + a) x ++ l := by
  intro a
  induction a with
  | zero => rfl
  | succ p ih =>
    have h1 : List.replicate (p + 1) x ++ (List.replicate b x ++ l)
        = x :: (List.replicate p x ++ (List.replicate b x ++ l)) := rfl
    have h2 : List.replicate (b + (p + 1)) x ++ l
        = x :: (List.replicate (b + p) x ++ l) := rfl
    rw [h1, h2, ih]

private theorem shiRl_repl_add {al : Type} (x : al) : ∀ a b : ℕ,
    List.replicate (a + b) x = List.replicate a x ++ List.replicate b x := by
  intro a b
  have h := shiRl_repl_join b x ([] : List al) a
  rw [List.append_nil, List.append_nil] at h
  have he : b + a = a + b := by omega
  rw [he] at h
  exact h.symm

/-! ### One-`stepAux`-node lemmas

`Turing.TM2.stepAux` recurses through an ENTIRE `Stmt` tree inside ONE `Turing.TM2.step`, so
a straight-line block costs ONE step. -/

private theorem shiRl_aux_pop {K : Type} [DecidableEq K] {Gam : K → Type} {Lam sig : Type}
    (k : K) (f : sig → Option (Gam k) → sig) (Q : Stmt Gam Lam sig) (v : sig)
    (S : ∀ j, List (Gam j)) :
    stepAux (Stmt.pop k f Q) v S
      = stepAux Q (f v (S k).head?) (Function.update S k (S k).tail) := rfl

private theorem shiRl_aux_push {K : Type} [DecidableEq K] {Gam : K → Type} {Lam sig : Type}
    (k : K) (f : sig → Gam k) (Q : Stmt Gam Lam sig) (v : sig) (S : ∀ j, List (Gam j)) :
    stepAux (Stmt.push k f Q) v S
      = stepAux Q v (Function.update S k (f v :: S k)) := rfl

private theorem shiRl_aux_bt {K : Type} [DecidableEq K] {Gam : K → Type} {Lam sig : Type}
    (g : sig → Bool) (Q1 Q2 : Stmt Gam Lam sig) (v : sig) (S : ∀ j, List (Gam j))
    (hg : g v = true) :
    stepAux (Stmt.branch g Q1 Q2) v S = stepAux Q1 v S := by
  have h : stepAux (Stmt.branch g Q1 Q2) v S
      = cond (g v) (stepAux Q1 v S) (stepAux Q2 v S) := rfl
  rw [h, hg]
  all_goals rfl

private theorem shiRl_aux_bf {K : Type} [DecidableEq K] {Gam : K → Type} {Lam sig : Type}
    (g : sig → Bool) (Q1 Q2 : Stmt Gam Lam sig) (v : sig) (S : ∀ j, List (Gam j))
    (hg : g v = false) :
    stepAux (Stmt.branch g Q1 Q2) v S = stepAux Q2 v S := by
  have h : stepAux (Stmt.branch g Q1 Q2) v S
      = cond (g v) (stepAux Q1 v S) (stepAux Q2 v S) := rfl
  rw [h, hg]
  all_goals rfl

private theorem shiRl_aux_goto {K : Type} [DecidableEq K] {Gam : K → Type} {Lam sig : Type}
    (fl : sig → Lam) (v : sig) (S : ∀ j, List (Gam j)) :
    stepAux (Stmt.goto fl) v S = { l := some (fl v), var := v, stk := S } := rfl

/-- The `pop kl`, `branch` TRUE, `pop kv` composite: the `kl` update is invisible at `kv`. -/
private theorem shiRl_aux_tt {K : Type} [DecidableEq K] {Gam : K → Type} {Lam sig : Type}
    {kv kl : K} (hvl : kv ≠ kl)
    (fL : sig → Option (Gam kl) → sig) (gL : sig → Bool)
    (fV : sig → Option (Gam kv) → sig)
    (Q1 Q2 : Stmt Gam Lam sig) (v : sig) (S : ∀ j, List (Gam j))
    (hg : gL (fL v (S kl).head?) = true) :
    stepAux (Stmt.pop kl fL (Stmt.branch gL (Stmt.pop kv fV Q1) Q2)) v S
      = stepAux Q1 (fV (fL v (S kl).head?) (S kv).head?)
          (Function.update (Function.update S kl (S kl).tail) kv (S kv).tail) := by
  rw [shiRl_aux_pop kl fL _ v S, shiRl_aux_bt gL _ _ _ _ hg,
    shiRl_aux_pop kv fV Q1 (fL v (S kl).head?) (Function.update S kl (S kl).tail),
    Function.update_of_ne hvl ((S kl).tail) S]
  all_goals rfl

/-! ### The three one-`step` transitions of the fused dispatch body at `l1` -/

/-- Continuing round: `kl` gave a LENGTH MARK and `kv` gave a cell, so one mark is banked. -/
private theorem shiRl_step_cont {K : Type} [DecidableEq K] {Gam : K → Type} {Lam sig : Type}
    (M : Lam → Stmt Gam Lam sig) {kv kl kd : K}
    (hvl : kv ≠ kl) (hvd : kv ≠ kd) (hld : kl ≠ kd) {l1 la lf : Lam}
    {fL : sig → Option (Gam kl) → sig} {gL : sig → Bool}
    {fV : sig → Option (Gam kv) → sig} {gV : sig → Bool}
    {md : sig → Gam kd} {mdc : Gam kd} {ml : Gam kl}
    (hM1 : M l1 = Stmt.pop kl fL (Stmt.branch gL
             (Stmt.pop kv fV (Stmt.branch gV
               (Stmt.push kd md (Stmt.goto (fun _ => l1)))
               (Stmt.goto (fun _ => lf))))
             (Stmt.goto (fun _ => la))))
    (hLm : ∀ w : sig, gL (fL w (some ml)) = true)
    (hVs : ∀ (w : sig) (y : Gam kv), gV (fV w (some y)) = true)
    (hmd : ∀ w : sig, md w = mdc) :
    ∀ (v : sig) (S : ∀ k, List (Gam k)) (w' : List (Gam kl))
      (z : Gam kv) (u' : List (Gam kv)),
      S kl = ml :: w' → S kv = z :: u' →
      step M { l := some l1, var := v, stk := S }
        = some { l := some l1, var := fV (fL v (some ml)) (some z),
                 stk := Function.update (Function.update (Function.update S kl w') kv u') kd
                          (mdc :: S kd) } := by
  intro v S w' z u' hSl hSv
  have h0 : step M { l := some l1, var := v, stk := S }
      = some (stepAux (M l1) v S) := rfl
  have hg1 : gL (fL v (S kl).head?) = true := by
    rw [hSl]
    exact hLm v
  rw [h0, hM1, shiRl_aux_tt hvl fL gL fV _ _ v S hg1, hSl, hSv]
  simp only [List.head?_cons, List.tail_cons]
  rw [shiRl_aux_bt gV _ _ _ _ (hVs (fL v (some ml)) z), shiRl_aux_push kd md _ _ _,
    Function.update_of_ne (Ne.symm hvd) u' (Function.update S kl w'),
    Function.update_of_ne (Ne.symm hld) w' S, hmd (fV (fL v (some ml)) (some z)),
    shiRl_aux_goto]
  all_goals rfl

/-- Exit to `la` (ADVANCE): the `kl` pop returned the DELIMITER, so `a <= w`.  `kv` is not
touched, and the delimiter cell is consumed. -/
private theorem shiRl_step_exitA {K : Type} [DecidableEq K] {Gam : K → Type} {Lam sig : Type}
    (M : Lam → Stmt Gam Lam sig) {kv kl kd : K} {l1 la lf : Lam}
    {fL : sig → Option (Gam kl) → sig} {gL : sig → Bool}
    {fV : sig → Option (Gam kv) → sig} {gV : sig → Bool}
    {md : sig → Gam kd} {dl : Gam kl}
    (hM1 : M l1 = Stmt.pop kl fL (Stmt.branch gL
             (Stmt.pop kv fV (Stmt.branch gV
               (Stmt.push kd md (Stmt.goto (fun _ => l1)))
               (Stmt.goto (fun _ => lf))))
             (Stmt.goto (fun _ => la))))
    (hLd : ∀ w : sig, gL (fL w (some dl)) = false) :
    ∀ (v : sig) (S : ∀ k, List (Gam k)) (w' : List (Gam kl)), S kl = dl :: w' →
      step M { l := some l1, var := v, stk := S }
        = some { l := some la, var := fL v (some dl),
                 stk := Function.update S kl w' } := by
  intro v S w' hSl
  have h0 : step M { l := some l1, var := v, stk := S }
      = some (stepAux (M l1) v S) := rfl
  have hg : gL (fL v (S kl).head?) = false := by
    rw [hSl]
    exact hLd v
  rw [h0, hM1, shiRl_aux_pop kl fL _ v S, shiRl_aux_bf gL _ _ _ _ hg, shiRl_aux_goto, hSl]
  all_goals (first | rfl | simp)

/-- Exit to `lf` (FOUND): `kl` gave a length mark but the `kv` pop returned `none`, so
`w < a`.  One length mark is consumed. -/
private theorem shiRl_step_exitF {K : Type} [DecidableEq K] {Gam : K → Type} {Lam sig : Type}
    (M : Lam → Stmt Gam Lam sig) {kv kl kd : K} (hvl : kv ≠ kl) {l1 la lf : Lam}
    {fL : sig → Option (Gam kl) → sig} {gL : sig → Bool}
    {fV : sig → Option (Gam kv) → sig} {gV : sig → Bool}
    {md : sig → Gam kd} {ml : Gam kl}
    (hM1 : M l1 = Stmt.pop kl fL (Stmt.branch gL
             (Stmt.pop kv fV (Stmt.branch gV
               (Stmt.push kd md (Stmt.goto (fun _ => l1)))
               (Stmt.goto (fun _ => lf))))
             (Stmt.goto (fun _ => la))))
    (hLm : ∀ w : sig, gL (fL w (some ml)) = true)
    (hVn : ∀ w : sig, gV (fV w none) = false) :
    ∀ (v : sig) (S : ∀ k, List (Gam k)) (w' : List (Gam kl)),
      S kl = ml :: w' → S kv = [] →
      step M { l := some l1, var := v, stk := S }
        = some { l := some lf, var := fV (fL v (some ml)) none,
                 stk := Function.update (Function.update S kl w') kv [] } := by
  intro v S w' hSl hSv
  have h0 : step M { l := some l1, var := v, stk := S }
      = some (stepAux (M l1) v S) := rfl
  have hg1 : gL (fL v (S kl).head?) = true := by
    rw [hSl]
    exact hLm v
  rw [h0, hM1, shiRl_aux_tt hvl fL gL fV _ _ v S hg1, hSl, hSv]
  simp only [List.head?_cons, List.tail_cons, List.head?_nil, List.tail_nil]
  rw [shiRl_aux_bf gV _ _ _ _ (hVn (fL v (some ml))), shiRl_aux_goto]
  all_goals rfl

/-! ### The banking comparison induction

`r` full rounds at `l1`, each consuming one length mark from `kl` AND one mark from `kv` and
banking one `mdc` on `kd`.  The post-state is an OPAQUE `T` with pointwise specs, which is the
only way to keep `Function.update` towers out of the induction. -/

/-! ### The two RESIDUAL-LENGTH recursions

The walk consumes `kl` and `kb` destructively, and WIRE-2's postcondition only BOUNDS what is
left.  What is left is in fact pinned by `(ps, w)`, by the very same descent that computes the
index: on the FOUND piece `(a, b)` -- the one with `w < a` -- the length stack retains the
`a - w` unread symbols of that piece's block (`a - w - 1` marks and its delimiter) followed by
the whole of `PL t`, while the base stack retains exactly `PB t`; on every ADVANCE piece both
stacks are emptied of that piece's block and the walk recurses on `(t, w - a)`.  Since
`(PL t).length = sum over t of (len + 1)` and `(PB t).length = sum over t of (base + 1)`, the
two residual lengths are the recursions

    R1 ((a, b) :: t) w = if w < a then (a - w) + sum over t of (len  + 1) else R1 t (w - a)
    R2 ((a, b) :: t) w = if w < a then           sum over t of (base + 1) else R2 t (w - a)

with `R1 [] w = R2 [] w = 0`.  `hPLc`/`hPBc` say nothing about `PL []` and `PB []`, so the
walk below proves `(T kl).length = R1 ps w + (PL []).length`; the public statement adds
`PL [] = []` and `PB [] = []` -- which every packing satisfies, and which the concrete
witness discharges by `rfl` -- to get the exact equations in the form an exact-cost
composition consumes. -/

private def shiRlR1 : List (ℕ × ℕ) → ℕ → ℕ
  | [], _ => 0
  | p :: t, w =>
      if w < p.1 then (p.1 - w) + (t.map (fun q => q.1 + 1)).sum else shiRlR1 t (w - p.1)

private def shiRlR2 : List (ℕ × ℕ) → ℕ → ℕ
  | [], _ => 0
  | p :: t, w =>
      if w < p.1 then (t.map (fun q => q.2 + 1)).sum else shiRlR2 t (w - p.1)

private theorem shiRlR10 : ∀ w : ℕ, shiRlR1 [] w = 0 := by
  intro w
  first
    | rfl
    | simp [shiRlR1]

private theorem shiRlR1c : ∀ (a b : ℕ) (t : List (ℕ × ℕ)) (w : ℕ),
    shiRlR1 ((a, b) :: t) w
      = if w < a then (a - w) + (t.map (fun p => p.1 + 1)).sum else shiRlR1 t (w - a) := by
  intro a b t w
  first
    | rfl
    | simp [shiRlR1]

private theorem shiRlR20 : ∀ w : ℕ, shiRlR2 [] w = 0 := by
  intro w
  first
    | rfl
    | simp [shiRlR2]

private theorem shiRlR2c : ∀ (a b : ℕ) (t : List (ℕ × ℕ)) (w : ℕ),
    shiRlR2 ((a, b) :: t) w
      = if w < a then (t.map (fun p => p.2 + 1)).sum else shiRlR2 t (w - a) := by
  intro a b t w
  first
    | rfl
    | simp [shiRlR2]

/-- The packed length stack has `sum over pieces of (len + 1)` symbols above `PL []`. -/
private theorem shiRl_PL_len {al : Type} (ml dl : al) (PL : List (ℕ × ℕ) → List al)
    (hPLc : ∀ (a b : ℕ) (t : List (ℕ × ℕ)),
      PL ((a, b) :: t) = List.replicate a ml ++ dl :: PL t) :
    ∀ ps : List (ℕ × ℕ),
      (PL ps).length = (ps.map (fun p => p.1 + 1)).sum + (PL ([] : List (ℕ × ℕ))).length := by
  intro ps
  induction ps with
  | nil => simp
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    have h1 : (PL ((a, b) :: t)).length = a + ((PL t).length + 1) := by
      rw [hPLc]
      simp only [List.length_append, List.length_cons, shiRl_len_repl]
    have h2 : (((a, b) :: t).map (fun p => p.1 + 1)).sum
        = (a + 1) + (t.map (fun p => p.1 + 1)).sum := by
      simp only [List.map_cons, List.sum_cons]
    rw [h1, h2, ih]
    omega

/-- The packed base stack has `sum over pieces of (base + 1)` symbols above `PB []`. -/
private theorem shiRl_PB_len {al : Type} (mb db : al) (PB : List (ℕ × ℕ) → List al)
    (hPBc : ∀ (a b : ℕ) (t : List (ℕ × ℕ)),
      PB ((a, b) :: t) = List.replicate b mb ++ db :: PB t) :
    ∀ ps : List (ℕ × ℕ),
      (PB ps).length = (ps.map (fun p => p.2 + 1)).sum + (PB ([] : List (ℕ × ℕ))).length := by
  intro ps
  induction ps with
  | nil => simp
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    have h1 : (PB ((a, b) :: t)).length = b + ((PB t).length + 1) := by
      rw [hPBc]
      simp only [List.length_append, List.length_cons, shiRl_len_repl]
    have h2 : (((a, b) :: t).map (fun p => p.2 + 1)).sum
        = (b + 1) + (t.map (fun p => p.2 + 1)).sum := by
      simp only [List.map_cons, List.sum_cons]
    rw [h1, h2, ih]
    omega

/-- `R1` never exceeds the packed length stack's own height. -/
private theorem shiRl_R1_le (R1 : List (ℕ × ℕ) → ℕ → ℕ)
    (hR10 : ∀ w : ℕ, R1 [] w = 0)
    (hR1c : ∀ (a b : ℕ) (t : List (ℕ × ℕ)) (w : ℕ),
      R1 ((a, b) :: t) w
        = if w < a then (a - w) + (t.map (fun p => p.1 + 1)).sum else R1 t (w - a)) :
    ∀ (ps : List (ℕ × ℕ)) (w : ℕ), R1 ps w ≤ (ps.map (fun p => p.1 + 1)).sum := by
  intro ps
  induction ps with
  | nil =>
    intro w
    rw [hR10]
    exact Nat.zero_le _
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    intro w
    have h2 : (((a, b) :: t).map (fun p => p.1 + 1)).sum
        = (a + 1) + (t.map (fun p => p.1 + 1)).sum := by
      simp only [List.map_cons, List.sum_cons]
    rw [h2, hR1c]
    rcases Nat.lt_or_ge w a with hf | hg
    · rw [if_pos hf]
      omega
    · rw [if_neg (Nat.not_lt.mpr hg)]
      have := ih (w - a)
      omega

/-- `R2` never exceeds the packed base stack's own height. -/
private theorem shiRl_R2_le (R2 : List (ℕ × ℕ) → ℕ → ℕ)
    (hR20 : ∀ w : ℕ, R2 [] w = 0)
    (hR2c : ∀ (a b : ℕ) (t : List (ℕ × ℕ)) (w : ℕ),
      R2 ((a, b) :: t) w
        = if w < a then (t.map (fun p => p.2 + 1)).sum else R2 t (w - a)) :
    ∀ (ps : List (ℕ × ℕ)) (w : ℕ), R2 ps w ≤ (ps.map (fun p => p.2 + 1)).sum := by
  intro ps
  induction ps with
  | nil =>
    intro w
    rw [hR20]
    exact Nat.zero_le _
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    intro w
    have h2 : (((a, b) :: t).map (fun p => p.2 + 1)).sum
        = (b + 1) + (t.map (fun p => p.2 + 1)).sum := by
      simp only [List.map_cons, List.sum_cons]
    rw [h2, hR2c]
    rcases Nat.lt_or_ge w a with hf | hg
    · rw [if_pos hf]
      omega
    · rw [if_neg (Nat.not_lt.mpr hg)]
      have := ih (w - a)
      omega
private theorem shiRl_core {K : Type} [DecidableEq K] {Gam : K → Type} {Lam sig : Type}
    (M : Lam → Stmt Gam Lam sig) {kv kl kd : K}
    (hvl : kv ≠ kl) (hvd : kv ≠ kd) (hld : kl ≠ kd) {l1 la lf : Lam}
    {fL : sig → Option (Gam kl) → sig} {gL : sig → Bool}
    {fV : sig → Option (Gam kv) → sig} {gV : sig → Bool}
    {md : sig → Gam kd} {mdc : Gam kd} {ml : Gam kl} {mv : Gam kv}
    (hM1 : M l1 = Stmt.pop kl fL (Stmt.branch gL
             (Stmt.pop kv fV (Stmt.branch gV
               (Stmt.push kd md (Stmt.goto (fun _ => l1)))
               (Stmt.goto (fun _ => lf))))
             (Stmt.goto (fun _ => la))))
    (hLm : ∀ w : sig, gL (fL w (some ml)) = true)
    (hVs : ∀ (w : sig) (y : Gam kv), gV (fV w (some y)) = true)
    (hmd : ∀ w : sig, md w = mdc) :
    ∀ (r : ℕ) (pl : List (Gam kl)) (pv : List (Gam kv)) (v : sig)
      (S T : ∀ k, List (Gam k)),
      S kl = List.replicate r ml ++ pl → S kv = List.replicate r mv ++ pv →
      T kl = pl → T kv = pv → T kd = List.replicate r mdc ++ S kd →
      (∀ k, k ≠ kl → k ≠ kv → k ≠ kd → T k = S k) →
      ∃ v' : sig,
        (fun cf : Option (Cfg Gam Lam sig) => cf.bind (step M))^[r]
            (some { l := some l1, var := v, stk := S })
          = some { l := some l1, var := v', stk := T } := by
  intro r
  induction r with
  | zero =>
    intro pl pv v S T hSl hSv hTl hTv hTd hTo
    have hTS : T = S := by
      funext k
      by_cases h1 : k = kl
      · subst h1
        rw [hTl, hSl]
        all_goals (first | rfl | simp)
      · by_cases h2 : k = kv
        · subst h2
          rw [hTv, hSv]
          all_goals (first | rfl | simp)
        · by_cases h3 : k = kd
          · subst h3
            rw [hTd]
            all_goals (first | rfl | simp)
          · exact hTo k h1 h2 h3
    refine ⟨v, ?_⟩
    rw [hTS]
    all_goals (first | rfl | simp)
  | succ q ih =>
    intro pl pv v S T hSl hSv hTl hTv hTd hTo
    have hSl' : S kl = ml :: (List.replicate q ml ++ pl) := by
      rw [hSl]
      all_goals (first | rfl | simp)
    have hSv' : S kv = mv :: (List.replicate q mv ++ pv) := by
      rw [hSv]
      all_goals (first | rfl | simp)
    have h1 : step M { l := some l1, var := v, stk := S }
        = some { l := some l1, var := fV (fL v (some ml)) (some mv),
                 stk := Function.update (Function.update (Function.update S kl
                          (List.replicate q ml ++ pl)) kv
                          (List.replicate q mv ++ pv)) kd (mdc :: S kd) } :=
      shiRl_step_cont M hvl hvd hld hM1 hLm hVs hmd v S (List.replicate q ml ++ pl) mv
        (List.replicate q mv ++ pv) hSl' hSv'
    have hS1l : (Function.update (Function.update (Function.update S kl
        (List.replicate q ml ++ pl)) kv (List.replicate q mv ++ pv)) kd
        (mdc :: S kd)) kl = List.replicate q ml ++ pl := by
      simp only [Function.update_of_ne hld, Function.update_of_ne (Ne.symm hvl),
        Function.update_self]
    have hS1v : (Function.update (Function.update (Function.update S kl
        (List.replicate q ml ++ pl)) kv (List.replicate q mv ++ pv)) kd
        (mdc :: S kd)) kv = List.replicate q mv ++ pv := by
      simp only [Function.update_of_ne hvd, Function.update_self]
    have hS1d : (Function.update (Function.update (Function.update S kl
        (List.replicate q ml ++ pl)) kv (List.replicate q mv ++ pv)) kd
        (mdc :: S kd)) kd = mdc :: S kd := by
      simp only [Function.update_self]
    have hS1o : ∀ k, k ≠ kl → k ≠ kv → k ≠ kd →
        (Function.update (Function.update (Function.update S kl
          (List.replicate q ml ++ pl)) kv (List.replicate q mv ++ pv)) kd
          (mdc :: S kd)) k = S k := by
      intro k ha hb hc
      simp only [Function.update_of_ne hc, Function.update_of_ne hb, Function.update_of_ne ha]
    have hTd' : T kd = List.replicate q mdc
        ++ (Function.update (Function.update (Function.update S kl
            (List.replicate q ml ++ pl)) kv (List.replicate q mv ++ pv)) kd
            (mdc :: S kd)) kd := by
      rw [hS1d, hTd, shiRl_repl_snoc]
    have hTo' : ∀ k, k ≠ kl → k ≠ kv → k ≠ kd →
        T k = (Function.update (Function.update (Function.update S kl
          (List.replicate q ml ++ pl)) kv (List.replicate q mv ++ pv)) kd
          (mdc :: S kd)) k := by
      intro k ha hb hc
      rw [hTo k ha hb hc, hS1o k ha hb hc]
    obtain ⟨v', hv'⟩ := ih pl pv (fV (fL v (some ml)) (some mv))
      (Function.update (Function.update (Function.update S kl
        (List.replicate q ml ++ pl)) kv (List.replicate q mv ++ pv)) kd (mdc :: S kd))
      T hS1l hS1v hTl hTv hTd' hTo'
    have hstep : (some { l := some l1, var := v, stk := S } :
          Option (Cfg Gam Lam sig)).bind (step M)
        = some { l := some l1, var := fV (fL v (some ml)) (some mv),
                 stk := Function.update (Function.update (Function.update S kl
                          (List.replicate q ml ++ pl)) kv
                          (List.replicate q mv ++ pv)) kd (mdc :: S kd) } := h1
    refine ⟨v', ?_⟩
    rw [Function.iterate_succ_apply, hstep]
    exact hv'

/-! ### The piece-list walk

Induction on the LIST OF PIECES.  The thirteen-piece layout dispatch is an instantiation of
this one theorem, not thirteen bespoke arms. -/

private theorem shiRl_walk {K : Type} [DecidableEq K] {Gam : K → Type} {Lam sig : Type}
    (M : Lam → Stmt Gam Lam sig) {kv kl kb kd ku kr : K}
    (hvl : kv ≠ kl) (hvb : kv ≠ kb) (hvd : kv ≠ kd) (hvu : kv ≠ ku) (hvr : kv ≠ kr)
    (hlb : kl ≠ kb) (hld : kl ≠ kd) (hlu : kl ≠ ku) (hlr : kl ≠ kr)
    (hbd : kb ≠ kd) (hbu : kb ≠ ku) (hbr : kb ≠ kr)
    (hdu : kd ≠ ku) (hdr : kd ≠ kr) (hur : ku ≠ kr)
    {l1 la la2 lf lo lend : Lam}
    {fL : sig → Option (Gam kl) → sig} {gL : sig → Bool}
    {fV : sig → Option (Gam kv) → sig} {gV : sig → Bool}
    {md : sig → Gam kd}
    {fD : sig → Option (Gam kd) → sig} {gD : sig → Bool} {hDp : sig → Gam kr}
    {fB : sig → Option (Gam kb) → sig} {gB : sig → Bool} {hPp : sig → Gam kr}
    {hQp : sig → Gam ku}
    {fO : sig → Option (Gam kd) → sig} {gO : sig → Bool} {hOp : sig → Gam ku}
    {eD : Gam kd → Gam kr} {eP : Gam kb → Gam kr}
    {eQ : Gam kb → Gam ku} {eO : Gam kd → Gam ku}
    (hM1 : M l1 = Stmt.pop kl fL (Stmt.branch gL
             (Stmt.pop kv fV (Stmt.branch gV
               (Stmt.push kd md (Stmt.goto (fun _ => l1)))
               (Stmt.goto (fun _ => lf))))
             (Stmt.goto (fun _ => la))))
    (hMa : M la = Stmt.pop kd fD (Stmt.branch gD
             (Stmt.push kr hDp (Stmt.goto (fun _ => la)))
             (Stmt.goto (fun _ => la2))))
    (hMa2 : M la2 = Stmt.pop kb fB (Stmt.branch gB
             (Stmt.push kr hPp (Stmt.goto (fun _ => la2)))
             (Stmt.goto (fun _ => l1))))
    (hMf : M lf = Stmt.pop kb fB (Stmt.branch gB
             (Stmt.push ku hQp (Stmt.goto (fun _ => lf)))
             (Stmt.goto (fun _ => lo))))
    (hMo : M lo = Stmt.pop kd fO (Stmt.branch gO
             (Stmt.push ku hOp (Stmt.goto (fun _ => lo)))
             (Stmt.goto (fun _ => lend))))
    {mv : Gam kv} {ml dl : Gam kl} {mb db : Gam kb} {mdc : Gam kd} {m : Gam ku}
    (hLm : ∀ w : sig, gL (fL w (some ml)) = true)
    (hLd : ∀ w : sig, gL (fL w (some dl)) = false)
    (hVs : ∀ (w : sig) (y : Gam kv), gV (fV w (some y)) = true)
    (hVn : ∀ w : sig, gV (fV w none) = false)
    (hmd : ∀ w : sig, md w = mdc)
    (hDs : ∀ (w : sig) (y : Gam kd), gD (fD w (some y)) = true)
    (hDn : ∀ w : sig, gD (fD w none) = false)
    (hDv : ∀ (w : sig) (y : Gam kd), hDp (fD w (some y)) = eD y)
    (hBm : ∀ w : sig, gB (fB w (some mb)) = true)
    (hBd : ∀ w : sig, gB (fB w (some db)) = false)
    (hPv : ∀ (w : sig) (y : Gam kb), hPp (fB w (some y)) = eP y)
    (hQv : ∀ (w : sig) (y : Gam kb), hQp (fB w (some y)) = eQ y)
    (hOs : ∀ (w : sig) (y : Gam kd), gO (fO w (some y)) = true)
    (hOn : ∀ w : sig, gO (fO w none) = false)
    (hOv : ∀ (w : sig) (y : Gam kd), hOp (fO w (some y)) = eO y)
    (hmQ : eQ mb = m) (hmO : eO mdc = m)
    (D C : List (ℕ × ℕ) → ℕ → ℕ)
    (hDc : ∀ (a b : ℕ) (t : List (ℕ × ℕ)) (w : ℕ),
      D ((a, b) :: t) w = if w < a then b + w else D t (w - a))
    (hCc : ∀ (a b : ℕ) (t : List (ℕ × ℕ)) (w : ℕ),
      C ((a, b) :: t) w = if w < a then 2 * w + b + 3 else 2 * a + b + 3 + C t (w - a))
    (PL : List (ℕ × ℕ) → List (Gam kl)) (PB : List (ℕ × ℕ) → List (Gam kb))
    (hPLc : ∀ (a b : ℕ) (t : List (ℕ × ℕ)),
      PL ((a, b) :: t) = List.replicate a ml ++ dl :: PL t)
    (hPBc : ∀ (a b : ℕ) (t : List (ℕ × ℕ)),
      PB ((a, b) :: t) = List.replicate b mb ++ db :: PB t)
    (R1 R2 : List (ℕ × ℕ) → ℕ → ℕ)
    (hR1c : ∀ (a b : ℕ) (t : List (ℕ × ℕ)) (w : ℕ),
      R1 ((a, b) :: t) w
        = if w < a then (a - w) + (t.map (fun p => p.1 + 1)).sum else R1 t (w - a))
    (hR2c : ∀ (a b : ℕ) (t : List (ℕ × ℕ)) (w : ℕ),
      R2 ((a, b) :: t) w
        = if w < a then (t.map (fun p => p.2 + 1)).sum else R2 t (w - a)) :
    ∀ (ps : List (ℕ × ℕ)) (w : ℕ) (v : sig) (S : ∀ k, List (Gam k)),
      w < (ps.map Prod.fst).sum →
      S kv = List.replicate w mv → S kl = PL ps → S kb = PB ps → S kd = [] →
      ∃ (v' : sig) (T : ∀ k, List (Gam k)),
        (fun cf : Option (Cfg Gam Lam sig) => cf.bind (step M))^[C ps w]
            (some { l := some l1, var := v, stk := S })
          = some { l := some lend, var := v', stk := T }
        ∧ T ku = List.replicate (D ps w) m ++ S ku
        ∧ T kv = []
        ∧ T kd = []
        ∧ (T kl).length = R1 ps w + (PL ([] : List (ℕ × ℕ))).length
        ∧ (T kb).length = R2 ps w + (PB ([] : List (ℕ × ℕ))).length
        ∧ (∀ k, k ≠ kv → k ≠ kl → k ≠ kb → k ≠ kd → k ≠ ku → k ≠ kr → T k = S k) := by
  have hlv : kl ≠ kv := Ne.symm hvl
  have hbv : kb ≠ kv := Ne.symm hvb
  have hdv : kd ≠ kv := Ne.symm hvd
  have huv : ku ≠ kv := Ne.symm hvu
  have hrv : kr ≠ kv := Ne.symm hvr
  have hbl : kb ≠ kl := Ne.symm hlb
  have hdl : kd ≠ kl := Ne.symm hld
  have hul : ku ≠ kl := Ne.symm hlu
  have hrl : kr ≠ kl := Ne.symm hlr
  have hdb : kd ≠ kb := Ne.symm hbd
  have hub : ku ≠ kb := Ne.symm hbu
  have hrb : kr ≠ kb := Ne.symm hbr
  have hud : ku ≠ kd := Ne.symm hdu
  have hrd : kr ≠ kd := Ne.symm hdr
  have hru : kr ≠ ku := Ne.symm hur
  intro ps
  induction ps with
  | nil =>
    intro w v S hlt _ _ _ _
    have h0 : ((([] : List (ℕ × ℕ))).map Prod.fst).sum = 0 := by
      first
        | rfl
        | simp
    rw [h0] at hlt
    exact absurd hlt (by omega)
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    intro w v S hlt hSv hSl hSb hSd
    have hsum : (((a, b) :: t).map Prod.fst).sum = a + (t.map Prod.fst).sum := by
      first
        | rfl
        | simp
    rw [hsum] at hlt
    have hSl' : S kl = List.replicate a ml ++ dl :: PL t := by rw [hSl, hPLc]
    have hSb' : S kb = List.replicate b mb ++ db :: PB t := by rw [hSb, hPBc]
    have hcontP : ∀ (x : sig) (y : Gam kb), y ∈ List.replicate b mb →
        gB (fB x (some y)) = true := by
      intro x y hy
      rw [List.eq_of_mem_replicate hy]
      exact hBm x
    rcases Nat.lt_or_ge w a with hfound | hadv
    · -- FOUND: `w < a`, so `kv` empties first and the bank holds the residual index `w`
      have hDval : D ((a, b) :: t) w = b + w := by
        rw [hDc, if_pos hfound]
      have hCval : C ((a, b) :: t) w = ((w + 1) + (b + 1)) + (w + 1) := by
        rw [hCc, if_pos hfound]
        omega
      have hja := shiRl_repl_join (a - w) ml (dl :: PL t) w
      have hea : a - w + w = a := by omega
      rw [hea] at hja
      obtain ⟨kk, hkk⟩ : ∃ kk : ℕ, a - w = kk + 1 := ⟨a - w - 1, by omega⟩
      have hcons : List.replicate (a - w) ml ++ dl :: PL t
          = ml :: (List.replicate kk ml ++ dl :: PL t) := by
        rw [hkk]
        all_goals (first | rfl | simp)
      have hSlsplit : S kl = List.replicate w ml
          ++ (ml :: (List.replicate (kk) ml ++ dl :: PL t)) := by
        rw [hSl', ← hja, hcons]
      have hSvsplit : S kv = List.replicate w mv ++ ([] : List (Gam kv)) := by
        rw [hSv, List.append_nil]
      obtain ⟨A, hA⟩ : ∃ T : ∀ k, List (Gam k),
          T = Function.update (Function.update (Function.update S kl
                (ml :: (List.replicate (kk) ml ++ dl :: PL t))) kv
                ([] : List (Gam kv))) kd (List.replicate w mdc) := ⟨_, rfl⟩
      have hAl : A kl = ml :: (List.replicate (kk) ml ++ dl :: PL t) := by
        rw [hA]
        simp only [Function.update_of_ne hld, Function.update_of_ne hlv, Function.update_self]
      have hAv : A kv = [] := by
        rw [hA]
        simp only [Function.update_of_ne hvd, Function.update_self]
      have hAd : A kd = List.replicate w mdc := by
        rw [hA]
        simp only [Function.update_self]
      have hAdc : A kd = List.replicate w mdc ++ S kd := by
        rw [hAd, hSd, List.append_nil]
      have hAo : ∀ k, k ≠ kl → k ≠ kv → k ≠ kd → A k = S k := by
        intro k h1 h2 h3
        rw [hA]
        simp only [Function.update_of_ne h3, Function.update_of_ne h2, Function.update_of_ne h1]
      obtain ⟨v0, hcore⟩ := shiRl_core M hvl hvd hld hM1 hLm hVs hmd w
        (ml :: (List.replicate (kk) ml ++ dl :: PL t)) ([] : List (Gam kv)) v S A
        hSlsplit hSvsplit hAl hAv hAdc hAo
      obtain ⟨B, hB⟩ : ∃ T : ∀ k, List (Gam k),
          T = Function.update (Function.update A kl
                (List.replicate (kk) ml ++ dl :: PL t)) kv ([] : List (Gam kv)) := ⟨_, rfl⟩
      have hexit : step M { l := some l1, var := v0, stk := A }
          = some { l := some lf, var := fV (fL v0 (some ml)) none, stk := B } := by
        rw [hB]
        exact shiRl_step_exitF M hvl hM1 hLm hVn v0 A
          (List.replicate (kk) ml ++ dl :: PL t) hAl hAv
      have hstep : (some { l := some l1, var := v0, stk := A } :
            Option (Cfg Gam Lam sig)).bind (step M)
          = some { l := some lf, var := fV (fL v0 (some ml)) none, stk := B } := hexit
      have e1 : (fun cf : Option (Cfg Gam Lam sig) => cf.bind (step M))^[w + 1]
          (some { l := some l1, var := v, stk := S })
          = some { l := some lf, var := fV (fL v0 (some ml)) none, stk := B } := by
        rw [Function.iterate_succ_apply', hcore]
        exact hstep
      have hBl : B kl = List.replicate (kk) ml ++ dl :: PL t := by
        rw [hB]
        simp only [Function.update_of_ne hlv, Function.update_self]
      have hBv : B kv = [] := by
        rw [hB]
        simp only [Function.update_self]
      have hBb : B kb = List.replicate b mb ++ db :: PB t := by
        rw [hB]
        simp only [Function.update_of_ne hbv, Function.update_of_ne hbl, hAo kb hbl hbv hbd,
          hSb']
      have hBd' : B kd = List.replicate w mdc := by
        rw [hB]
        simp only [Function.update_of_ne hdv, Function.update_of_ne hdl, hAd]
      have hBu : B ku = S ku := by
        rw [hB]
        simp only [Function.update_of_ne huv, Function.update_of_ne hul,
          hAo ku hul huv hud]
      have hBo : ∀ k, k ≠ kv → k ≠ kl → k ≠ kb → k ≠ kd → k ≠ ku → k ≠ kr → B k = S k := by
        intro k h1 h2 h3 h4 h5 h6
        rw [hB]
        simp only [Function.update_of_ne h1, Function.update_of_ne h2, hAo k h2 h1 h4]
      have hp2 := (ShiTM.branch_loop_transfers_prefix_until_symbol M hbu hMf hQv
        (List.replicate b mb) hcontP db hBd (PB t) (fV (fL v0 (some ml)) none) B hBb).1
      simp only [shiRl_len_repl, shiRl_map_rev, hmQ, hBu] at hp2
      obtain ⟨v2, C1, e2, hC1⟩ : ∃ (x : sig) (T : ∀ k, List (Gam k)),
          (fun cf : Option (Cfg Gam Lam sig) => cf.bind (step M))^[b + 1]
              (some { l := some lf, var := fV (fL v0 (some ml)) none, stk := B })
            = some { l := some lo, var := x, stk := T }
          ∧ T = Function.update (Function.update B kb (PB t)) ku
                  (List.replicate b m ++ S ku) := ⟨_, _, hp2, rfl⟩
      have hC1d : C1 kd = List.replicate w mdc := by
        rw [hC1]
        simp only [Function.update_of_ne hdu, Function.update_of_ne hdb, hBd']
      have hC1u : C1 ku = List.replicate b m ++ S ku := by
        rw [hC1]
        simp only [Function.update_self]
      have hC1v : C1 kv = [] := by
        rw [hC1]
        simp only [Function.update_of_ne hvu, Function.update_of_ne hvb, hBv]
      have hC1l : C1 kl = List.replicate (kk) ml ++ dl :: PL t := by
        rw [hC1]
        simp only [Function.update_of_ne hlu, Function.update_of_ne hlb, hBl]
      have hC1b : C1 kb = PB t := by
        rw [hC1]
        simp only [Function.update_of_ne hbu, Function.update_self]
      have hC1o : ∀ k, k ≠ kv → k ≠ kl → k ≠ kb → k ≠ kd → k ≠ ku → k ≠ kr →
          C1 k = S k := by
        intro k h1 h2 h3 h4 h5 h6
        rw [hC1]
        simp only [Function.update_of_ne h5, Function.update_of_ne h3,
          hBo k h1 h2 h3 h4 h5 h6]
      have hp3 := (ShiTM.copy_loop_transfers_stack M hdu hMo hOs hOn hOv
        (List.replicate w mdc) v2 C1 hC1d).1
      simp only [shiRl_len_repl, shiRl_map_rev, hmO, hC1u] at hp3
      obtain ⟨v3, T, e3, hT⟩ : ∃ (x : sig) (Q : ∀ k, List (Gam k)),
          (fun cf : Option (Cfg Gam Lam sig) => cf.bind (step M))^[w + 1]
              (some { l := some lo, var := v2, stk := C1 })
            = some { l := some lend, var := x, stk := Q }
          ∧ Q = Function.update (Function.update C1 kd ([] : List (Gam kd))) ku
                  (List.replicate w m ++ (List.replicate b m ++ S ku)) := ⟨_, _, hp3, rfl⟩
      refine ⟨v3, T, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hCval, Function.iterate_add_apply _ ((w + 1) + (b + 1)) (w + 1), e1,
          Function.iterate_add_apply _ (w + 1) (b + 1), e2, e3]
      · rw [hDval, hT]
        simp only [Function.update_self]
        exact shiRl_repl_join b m (S ku) w
      · rw [hT]
        simp only [Function.update_of_ne hvu, Function.update_of_ne hvd, hC1v]
      · rw [hT]
        simp only [Function.update_of_ne hdu, Function.update_self]
      · have h1 : T kl = List.replicate (kk) ml ++ dl :: PL t := by
          rw [hT]
          simp only [Function.update_of_ne hlu, Function.update_of_ne hld, hC1l]
        have h2 : (PL t).length
            = (t.map (fun p => p.1 + 1)).sum + (PL ([] : List (ℕ × ℕ))).length :=
          shiRl_PL_len ml dl PL hPLc t
        rw [hR1c, if_pos hfound, h1]
        simp only [List.length_append, List.length_cons, shiRl_len_repl, h2]
        omega
      · have h1 : T kb = PB t := by
          rw [hT]
          simp only [Function.update_of_ne hbu, Function.update_of_ne hbd, hC1b]
        rw [hR2c, if_pos hfound, h1]
        exact shiRl_PB_len mb db PB hPBc t
      · intro k h1 h2 h3 h4 h5 h6
        rw [hT]
        simp only [Function.update_of_ne h5, Function.update_of_ne h4,
          hC1o k h1 h2 h3 h4 h5 h6]
    · -- ADVANCE: `a <= w`, the length block empties first, the bank is cleared and the base
      -- block is discarded, and the walk re-enters `l1` on the TAIL of the piece list
      have hDval : D ((a, b) :: t) w = D t (w - a) := by
        rw [hDc, if_neg (Nat.not_lt.mpr hadv)]
      have hCval : C ((a, b) :: t) w
          = C t (w - a) + ((b + 1) + ((a + 1) + (a + 1))) := by
        rw [hCc, if_neg (Nat.not_lt.mpr hadv)]
        omega
      have hSvsplit : S kv = List.replicate a mv ++ List.replicate (w - a) mv := by
        rw [hSv, ← shiRl_repl_add mv a (w - a)]
        have hw : a + (w - a) = w := by omega
        rw [hw]
      obtain ⟨A, hA⟩ : ∃ T : ∀ k, List (Gam k),
          T = Function.update (Function.update (Function.update S kl (dl :: PL t)) kv
                (List.replicate (w - a) mv)) kd (List.replicate a mdc) := ⟨_, rfl⟩
      have hAl : A kl = dl :: PL t := by
        rw [hA]
        simp only [Function.update_of_ne hld, Function.update_of_ne hlv, Function.update_self]
      have hAv : A kv = List.replicate (w - a) mv := by
        rw [hA]
        simp only [Function.update_of_ne hvd, Function.update_self]
      have hAd : A kd = List.replicate a mdc := by
        rw [hA]
        simp only [Function.update_self]
      have hAdc : A kd = List.replicate a mdc ++ S kd := by
        rw [hAd, hSd, List.append_nil]
      have hAo : ∀ k, k ≠ kl → k ≠ kv → k ≠ kd → A k = S k := by
        intro k h1 h2 h3
        rw [hA]
        simp only [Function.update_of_ne h3, Function.update_of_ne h2, Function.update_of_ne h1]
      obtain ⟨v0, hcore⟩ := shiRl_core M hvl hvd hld hM1 hLm hVs hmd a (dl :: PL t)
        (List.replicate (w - a) mv) v S A hSl' hSvsplit hAl hAv hAdc hAo
      obtain ⟨B, hB⟩ : ∃ T : ∀ k, List (Gam k),
          T = Function.update A kl (PL t) := ⟨_, rfl⟩
      have hexit : step M { l := some l1, var := v0, stk := A }
          = some { l := some la, var := fL v0 (some dl), stk := B } := by
        rw [hB]
        exact shiRl_step_exitA M hM1 hLd v0 A (PL t) hAl
      have hstep : (some { l := some l1, var := v0, stk := A } :
            Option (Cfg Gam Lam sig)).bind (step M)
          = some { l := some la, var := fL v0 (some dl), stk := B } := hexit
      have e1 : (fun cf : Option (Cfg Gam Lam sig) => cf.bind (step M))^[a + 1]
          (some { l := some l1, var := v, stk := S })
          = some { l := some la, var := fL v0 (some dl), stk := B } := by
        rw [Function.iterate_succ_apply', hcore]
        exact hstep
      have hBl : B kl = PL t := by
        rw [hB]
        simp only [Function.update_self]
      have hBv : B kv = List.replicate (w - a) mv := by
        rw [hB]
        simp only [Function.update_of_ne hvl, hAv]
      have hBb : B kb = List.replicate b mb ++ db :: PB t := by
        rw [hB]
        simp only [Function.update_of_ne hbl, hAo kb hbl hbv hbd, hSb']
      have hBd' : B kd = List.replicate a mdc := by
        rw [hB]
        simp only [Function.update_of_ne hdl, hAd]
      have hBu : B ku = S ku := by
        rw [hB]
        simp only [Function.update_of_ne hul, hAo ku hul huv hud]
      have hBo : ∀ k, k ≠ kv → k ≠ kl → k ≠ kb → k ≠ kd → k ≠ ku → k ≠ kr → B k = S k := by
        intro k h1 h2 h3 h4 h5 h6
        rw [hB]
        simp only [Function.update_of_ne h2, hAo k h2 h1 h4]
      have hp2 := (ShiTM.copy_loop_transfers_stack M hdr hMa hDs hDn hDv
        (List.replicate a mdc) (fL v0 (some dl)) B hBd').1
      simp only [shiRl_len_repl, shiRl_map_rev] at hp2
      obtain ⟨v2, C1, e2, hC1⟩ : ∃ (x : sig) (Q : ∀ k, List (Gam k)),
          (fun cf : Option (Cfg Gam Lam sig) => cf.bind (step M))^[a + 1]
              (some { l := some la, var := fL v0 (some dl), stk := B })
            = some { l := some la2, var := x, stk := Q }
          ∧ Q = Function.update (Function.update B kd ([] : List (Gam kd))) kr
                  (List.replicate a (eD mdc) ++ B kr) := ⟨_, _, hp2, rfl⟩
      have hC1b : C1 kb = List.replicate b mb ++ db :: PB t := by
        rw [hC1]
        simp only [Function.update_of_ne hbr, Function.update_of_ne hbd, hBb]
      have hC1v : C1 kv = List.replicate (w - a) mv := by
        rw [hC1]
        simp only [Function.update_of_ne hvr, Function.update_of_ne hvd, hBv]
      have hC1l : C1 kl = PL t := by
        rw [hC1]
        simp only [Function.update_of_ne hlr, Function.update_of_ne hld, hBl]
      have hC1d : C1 kd = [] := by
        rw [hC1]
        simp only [Function.update_of_ne hdr, Function.update_self]
      have hC1u : C1 ku = S ku := by
        rw [hC1]
        simp only [Function.update_of_ne hur, Function.update_of_ne hud, hBu]
      have hC1o : ∀ k, k ≠ kv → k ≠ kl → k ≠ kb → k ≠ kd → k ≠ ku → k ≠ kr →
          C1 k = S k := by
        intro k h1 h2 h3 h4 h5 h6
        rw [hC1]
        simp only [Function.update_of_ne h6, Function.update_of_ne h4,
          hBo k h1 h2 h3 h4 h5 h6]
      have hp3 := (ShiTM.branch_loop_transfers_prefix_until_symbol M hbr hMa2 hPv
        (List.replicate b mb) hcontP db hBd (PB t) v2 C1 hC1b).1
      simp only [shiRl_len_repl, shiRl_map_rev] at hp3
      obtain ⟨v3, S3, e3, hS3⟩ : ∃ (x : sig) (Q : ∀ k, List (Gam k)),
          (fun cf : Option (Cfg Gam Lam sig) => cf.bind (step M))^[b + 1]
              (some { l := some la2, var := v2, stk := C1 })
            = some { l := some l1, var := x, stk := Q }
          ∧ Q = Function.update (Function.update C1 kb (PB t)) kr
                  (List.replicate b (eP mb) ++ C1 kr) := ⟨_, _, hp3, rfl⟩
      have hS3v : S3 kv = List.replicate (w - a) mv := by
        rw [hS3]
        simp only [Function.update_of_ne hvr, Function.update_of_ne hvb, hC1v]
      have hS3l : S3 kl = PL t := by
        rw [hS3]
        simp only [Function.update_of_ne hlr, Function.update_of_ne hlb, hC1l]
      have hS3b : S3 kb = PB t := by
        rw [hS3]
        simp only [Function.update_of_ne hbr, Function.update_self]
      have hS3d : S3 kd = [] := by
        rw [hS3]
        simp only [Function.update_of_ne hdr, Function.update_of_ne hdb, hC1d]
      have hS3u : S3 ku = S ku := by
        rw [hS3]
        simp only [Function.update_of_ne hur, Function.update_of_ne hub, hC1u]
      have hS3o : ∀ k, k ≠ kv → k ≠ kl → k ≠ kb → k ≠ kd → k ≠ ku → k ≠ kr →
          S3 k = S k := by
        intro k h1 h2 h3 h4 h5 h6
        rw [hS3]
        simp only [Function.update_of_ne h6, Function.update_of_ne h3,
          hC1o k h1 h2 h3 h4 h5 h6]
      have hlt' : w - a < (t.map Prod.fst).sum := by omega
      obtain ⟨v4, T, e4, hTu, hTv, hTd, hTl, hTb, hTo⟩ :=
        ih (w - a) v3 S3 hlt' hS3v hS3l hS3b hS3d
      refine ⟨v4, T, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hCval, Function.iterate_add_apply _ (C t (w - a)) ((b + 1) + ((a + 1) + (a + 1))),
          Function.iterate_add_apply _ (b + 1) ((a + 1) + (a + 1)),
          Function.iterate_add_apply _ (a + 1) (a + 1), e1, e2, e3, e4]
      · rw [hDval, hTu, hS3u]
      · exact hTv
      · exact hTd
      · rw [hR1c, if_neg (Nat.not_lt.mpr hadv)]
        exact hTl
      · rw [hR2c, if_neg (Nat.not_lt.mpr hadv)]
        exact hTb
      · intro k h1 h2 h3 h4 h5 h6
        rw [hTo k h1 h2 h3 h4 h5 h6, hS3o k h1 h2 h3 h4 h5 h6]
/-! ### The residual lengths, pinned

The same walk, with the two residual heights now EQUATIONS rather than bounds.  `hPL0` and
`hPB0` are what turn the walk's `R1 ps w + (PL []).length` into `R1 ps w`; they hold for every
packing that bottoms out on the empty stack, and the concrete witness below discharges both by
`rfl`. -/

private theorem shiRl_walk_exact
    {K : Type} [DecidableEq K] {Gam : K → Type} {Lam sig : Type}
    (M : Lam → Stmt Gam Lam sig) {kv kl kb kd ku kr : K}
    (hvl : kv ≠ kl) (hvb : kv ≠ kb) (hvd : kv ≠ kd) (hvu : kv ≠ ku) (hvr : kv ≠ kr)
    (hlb : kl ≠ kb) (hld : kl ≠ kd) (hlu : kl ≠ ku) (hlr : kl ≠ kr)
    (hbd : kb ≠ kd) (hbu : kb ≠ ku) (hbr : kb ≠ kr)
    (hdu : kd ≠ ku) (hdr : kd ≠ kr) (hur : ku ≠ kr)
    {l1 la la2 lf lo lend : Lam}
    {fL : sig → Option (Gam kl) → sig} {gL : sig → Bool}
    {fV : sig → Option (Gam kv) → sig} {gV : sig → Bool}
    {md : sig → Gam kd}
    {fD : sig → Option (Gam kd) → sig} {gD : sig → Bool} {hDp : sig → Gam kr}
    {fB : sig → Option (Gam kb) → sig} {gB : sig → Bool} {hPp : sig → Gam kr}
    {hQp : sig → Gam ku}
    {fO : sig → Option (Gam kd) → sig} {gO : sig → Bool} {hOp : sig → Gam ku}
    {eD : Gam kd → Gam kr} {eP : Gam kb → Gam kr}
    {eQ : Gam kb → Gam ku} {eO : Gam kd → Gam ku}
    (hM1 : M l1 = Stmt.pop kl fL (Stmt.branch gL
             (Stmt.pop kv fV (Stmt.branch gV
               (Stmt.push kd md (Stmt.goto (fun _ => l1)))
               (Stmt.goto (fun _ => lf))))
             (Stmt.goto (fun _ => la))))
    (hMa : M la = Stmt.pop kd fD (Stmt.branch gD
             (Stmt.push kr hDp (Stmt.goto (fun _ => la)))
             (Stmt.goto (fun _ => la2))))
    (hMa2 : M la2 = Stmt.pop kb fB (Stmt.branch gB
             (Stmt.push kr hPp (Stmt.goto (fun _ => la2)))
             (Stmt.goto (fun _ => l1))))
    (hMf : M lf = Stmt.pop kb fB (Stmt.branch gB
             (Stmt.push ku hQp (Stmt.goto (fun _ => lf)))
             (Stmt.goto (fun _ => lo))))
    (hMo : M lo = Stmt.pop kd fO (Stmt.branch gO
             (Stmt.push ku hOp (Stmt.goto (fun _ => lo)))
             (Stmt.goto (fun _ => lend))))
    {mv : Gam kv} {ml dl : Gam kl} {mb db : Gam kb} {mdc : Gam kd} {m : Gam ku}
    (hLm : ∀ w : sig, gL (fL w (some ml)) = true)
    (hLd : ∀ w : sig, gL (fL w (some dl)) = false)
    (hVs : ∀ (w : sig) (y : Gam kv), gV (fV w (some y)) = true)
    (hVn : ∀ w : sig, gV (fV w none) = false)
    (hmd : ∀ w : sig, md w = mdc)
    (hDs : ∀ (w : sig) (y : Gam kd), gD (fD w (some y)) = true)
    (hDn : ∀ w : sig, gD (fD w none) = false)
    (hDv : ∀ (w : sig) (y : Gam kd), hDp (fD w (some y)) = eD y)
    (hBm : ∀ w : sig, gB (fB w (some mb)) = true)
    (hBd : ∀ w : sig, gB (fB w (some db)) = false)
    (hPv : ∀ (w : sig) (y : Gam kb), hPp (fB w (some y)) = eP y)
    (hQv : ∀ (w : sig) (y : Gam kb), hQp (fB w (some y)) = eQ y)
    (hOs : ∀ (w : sig) (y : Gam kd), gO (fO w (some y)) = true)
    (hOn : ∀ w : sig, gO (fO w none) = false)
    (hOv : ∀ (w : sig) (y : Gam kd), hOp (fO w (some y)) = eO y)
    (hmQ : eQ mb = m) (hmO : eO mdc = m)
    (D C : List (ℕ × ℕ) → ℕ → ℕ)
    (hDc : ∀ (a b : ℕ) (t : List (ℕ × ℕ)) (w : ℕ),
      D ((a, b) :: t) w = if w < a then b + w else D t (w - a))
    (hCc : ∀ (a b : ℕ) (t : List (ℕ × ℕ)) (w : ℕ),
      C ((a, b) :: t) w = if w < a then 2 * w + b + 3 else 2 * a + b + 3 + C t (w - a))
    (PL : List (ℕ × ℕ) → List (Gam kl)) (PB : List (ℕ × ℕ) → List (Gam kb))
    (hPLc : ∀ (a b : ℕ) (t : List (ℕ × ℕ)),
      PL ((a, b) :: t) = List.replicate a ml ++ dl :: PL t)
    (hPBc : ∀ (a b : ℕ) (t : List (ℕ × ℕ)),
      PB ((a, b) :: t) = List.replicate b mb ++ db :: PB t)
    (hPL0 : PL ([] : List (ℕ × ℕ)) = [])
    (hPB0 : PB ([] : List (ℕ × ℕ)) = []) :
    ∀ (ps : List (ℕ × ℕ)) (w : ℕ) (v : sig) (S : ∀ k, List (Gam k)),
      w < (ps.map Prod.fst).sum →
      S kv = List.replicate w mv → S kl = PL ps → S kb = PB ps → S kd = [] →
      ∃ (v' : sig) (T : ∀ k, List (Gam k)),
        (fun cf : Option (Cfg Gam Lam sig) => cf.bind (step M))^[C ps w]
            (some { l := some l1, var := v, stk := S })
          = some { l := some lend, var := v', stk := T }
        ∧ T ku = List.replicate (D ps w) m ++ S ku
        ∧ T kv = []
        ∧ T kd = []
        ∧ (T kl).length = shiRlR1 ps w
        ∧ (T kb).length = shiRlR2 ps w
        ∧ shiRlR1 ps w ≤ (PL ps).length
        ∧ shiRlR2 ps w ≤ (PB ps).length
        ∧ (T kl).length ≤ (S kl).length
        ∧ (T kb).length ≤ (S kb).length
        ∧ (∀ k, k ≠ kv → k ≠ kl → k ≠ kb → k ≠ kd → k ≠ ku → k ≠ kr → T k = S k) := by
  intro ps w v S hlt hSv hSl hSb hSd
  obtain ⟨v', T, h1, h2, h3, h4, h5, h6, h7⟩ :=
    shiRl_walk M hvl hvb hvd hvu hvr hlb hld hlu hlr hbd hbu hbr hdu hdr hur
      hM1 hMa hMa2 hMf hMo hLm hLd hVs hVn hmd hDs hDn hDv hBm hBd hPv hQv hOs hOn hOv
      hmQ hmO D C hDc hCc PL PB hPLc hPBc shiRlR1 shiRlR2 shiRlR1c shiRlR2c
      ps w v S hlt hSv hSl hSb hSd
  have hpl : (PL ps).length
      = (ps.map (fun p => p.1 + 1)).sum + (PL ([] : List (ℕ × ℕ))).length :=
    shiRl_PL_len ml dl PL hPLc ps
  have hpb : (PB ps).length
      = (ps.map (fun p => p.2 + 1)).sum + (PB ([] : List (ℕ × ℕ))).length :=
    shiRl_PB_len mb db PB hPBc ps
  have hb1 : shiRlR1 ps w ≤ (ps.map (fun p => p.1 + 1)).sum :=
    shiRl_R1_le shiRlR1 shiRlR10 shiRlR1c ps w
  have hb2 : shiRlR2 ps w ≤ (ps.map (fun p => p.2 + 1)).sum :=
    shiRl_R2_le shiRlR2 shiRlR20 shiRlR2c ps w
  have hz1 : (PL ([] : List (ℕ × ℕ))).length = 0 := by
    rw [hPL0]
    rfl
  have hz2 : (PB ([] : List (ℕ × ℕ))).length = 0 := by
    rw [hPB0]
    rfl
  rw [hz1] at h5 hpl
  rw [hz2] at h6 hpb
  have hs1 : (S kl).length = (PL ps).length := by rw [hSl]
  have hs2 : (S kb).length = (PB ps).length := by rw [hSb]
  exact ⟨v', T, h1, h2, h3, h4, by omega, by omega, by omega, by omega, by omega,
    by omega, h7⟩
private def shiRlDd : List (ℕ × ℕ) → ℕ → ℕ
  | [], _ => 0
  | p :: t, w => if w < p.1 then p.2 + w else shiRlDd t (w - p.1)

private def shiRlCc : List (ℕ × ℕ) → ℕ → ℕ
  | [], _ => 0
  | p :: t, w => if w < p.1 then 2 * w + p.2 + 3 else 2 * p.1 + p.2 + 3 + shiRlCc t (w - p.1)

private theorem shiRlDd0 : ∀ w : ℕ, shiRlDd [] w = 0 := by
  intro w
  first
    | rfl
    | simp [shiRlDd]

private theorem shiRlDdc : ∀ (a b : ℕ) (t : List (ℕ × ℕ)) (w : ℕ),
    shiRlDd ((a, b) :: t) w = if w < a then b + w else shiRlDd t (w - a) := by
  intro a b t w
  first
    | rfl
    | simp [shiRlDd]

private theorem shiRlCc0 : ∀ w : ℕ, shiRlCc [] w = 0 := by
  intro w
  first
    | rfl
    | simp [shiRlCc]

private theorem shiRlCcc : ∀ (a b : ℕ) (t : List (ℕ × ℕ)) (w : ℕ),
    shiRlCc ((a, b) :: t) w
      = if w < a then 2 * w + b + 3 else 2 * a + b + 3 + shiRlCc t (w - a) := by
  intro a b t w
  first
    | rfl
    | simp [shiRlCc]

/-! ### A concrete witness machine on SIX distinct stacks

Five of the six stack alphabets are distinct types and two of them (`kl`, `kb`) carry TWO
symbols each -- a mark and a delimiter -- so the mark/delimiter guards are honest tests and
not a singleton degeneracy, and the `kb -> kr` recovery map is an injection.  `sig` is a
tagged union whose `nil` tag answers every "the pop returned none" guard while each `pX` tag
supplies its value-recovery law by `rfl`. -/

private inductive shiRlGv where
  | mv

private inductive shiRlGl where
  | ml
  | dl

private inductive shiRlGb where
  | mb
  | db

private inductive shiRlGd where
  | md1

private inductive shiRlGu where
  | m

private inductive shiRlGr where
  | r1
  | r2

private def shiRlAlpha : ℕ → Type
  | 0 => shiRlGv
  | 1 => shiRlGl
  | 2 => shiRlGb
  | 3 => shiRlGd
  | 4 => shiRlGu
  | _ => shiRlGr

private def shiRlGam (k : Fin 6) : Type := shiRlAlpha k.val

private def shiRlKv : Fin 6 := ⟨0, by omega⟩
private def shiRlKl : Fin 6 := ⟨1, by omega⟩
private def shiRlKb : Fin 6 := ⟨2, by omega⟩
private def shiRlKd : Fin 6 := ⟨3, by omega⟩
private def shiRlKu : Fin 6 := ⟨4, by omega⟩
private def shiRlKr : Fin 6 := ⟨5, by omega⟩

private inductive shiRlLam where
  | l1
  | la
  | la2
  | lf
  | lo
  | lend

private inductive shiRlSig where
  | nil
  | ok
  | pv : shiRlGv → shiRlSig
  | pl : shiRlGl → shiRlSig
  | pb : shiRlGb → shiRlSig
  | pd : shiRlGd → shiRlSig

private def shiRlGL : shiRlSig → Bool
  | .pl .ml => true
  | _ => false

private def shiRlGB : shiRlSig → Bool
  | .pb .mb => true
  | _ => false

private def shiRlGS : shiRlSig → Bool
  | .nil => false
  | _ => true

private def shiRlFL : shiRlSig → Option shiRlGl → shiRlSig
  | _, some y => .pl y
  | _, none => .nil

private def shiRlFV : shiRlSig → Option shiRlGv → shiRlSig
  | _, some y => .pv y
  | _, none => .nil

private def shiRlFB : shiRlSig → Option shiRlGb → shiRlSig
  | _, some y => .pb y
  | _, none => .nil

private def shiRlFD : shiRlSig → Option shiRlGd → shiRlSig
  | _, some y => .pd y
  | _, none => .nil

private def shiRlED : shiRlGd → shiRlGr
  | .md1 => .r1

private def shiRlEP : shiRlGb → shiRlGr
  | .mb => .r2
  | .db => .r1

private def shiRlEQ : shiRlGb → shiRlGu
  | .mb => .m
  | .db => .m

private def shiRlEO : shiRlGd → shiRlGu
  | .md1 => .m

private def shiRlHD : shiRlSig → shiRlGr
  | .pd y => shiRlED y
  | _ => .r1

private def shiRlHP : shiRlSig → shiRlGr
  | .pb y => shiRlEP y
  | _ => .r1

private def shiRlHQ : shiRlSig → shiRlGu
  | .pb y => shiRlEQ y
  | _ => .m

private def shiRlHO : shiRlSig → shiRlGu
  | .pd y => shiRlEO y
  | _ => .m

private def shiRlMD : shiRlSig → shiRlGd := fun _ => .md1

private def shiRlM : shiRlLam → Turing.TM2.Stmt shiRlGam shiRlLam shiRlSig
  | .l1 => Turing.TM2.Stmt.pop shiRlKl shiRlFL (Turing.TM2.Stmt.branch shiRlGL
             (Turing.TM2.Stmt.pop shiRlKv shiRlFV (Turing.TM2.Stmt.branch shiRlGS
               (Turing.TM2.Stmt.push shiRlKd shiRlMD
                 (Turing.TM2.Stmt.goto (fun _ => shiRlLam.l1)))
               (Turing.TM2.Stmt.goto (fun _ => shiRlLam.lf))))
             (Turing.TM2.Stmt.goto (fun _ => shiRlLam.la)))
  | .la => Turing.TM2.Stmt.pop shiRlKd shiRlFD (Turing.TM2.Stmt.branch shiRlGS
             (Turing.TM2.Stmt.push shiRlKr shiRlHD
               (Turing.TM2.Stmt.goto (fun _ => shiRlLam.la)))
             (Turing.TM2.Stmt.goto (fun _ => shiRlLam.la2)))
  | .la2 => Turing.TM2.Stmt.pop shiRlKb shiRlFB (Turing.TM2.Stmt.branch shiRlGB
             (Turing.TM2.Stmt.push shiRlKr shiRlHP
               (Turing.TM2.Stmt.goto (fun _ => shiRlLam.la2)))
             (Turing.TM2.Stmt.goto (fun _ => shiRlLam.l1)))
  | .lf => Turing.TM2.Stmt.pop shiRlKb shiRlFB (Turing.TM2.Stmt.branch shiRlGB
             (Turing.TM2.Stmt.push shiRlKu shiRlHQ
               (Turing.TM2.Stmt.goto (fun _ => shiRlLam.lf)))
             (Turing.TM2.Stmt.goto (fun _ => shiRlLam.lo)))
  | .lo => Turing.TM2.Stmt.pop shiRlKd shiRlFD (Turing.TM2.Stmt.branch shiRlGS
             (Turing.TM2.Stmt.push shiRlKu shiRlHO
               (Turing.TM2.Stmt.goto (fun _ => shiRlLam.lo)))
             (Turing.TM2.Stmt.goto (fun _ => shiRlLam.lend)))
  | .lend => Turing.TM2.Stmt.halt

private def shiRlPkL : List (ℕ × ℕ) → List shiRlGl
  | [] => []
  | p :: t => List.replicate p.1 shiRlGl.ml ++ shiRlGl.dl :: shiRlPkL t

private def shiRlPkB : List (ℕ × ℕ) → List shiRlGb
  | [] => []
  | p :: t => List.replicate p.2 shiRlGb.mb ++ shiRlGb.db :: shiRlPkB t

/-- The thirteen pieces of the amplifier layout at `n = 2`, `wit = 2`, `anc = 1`: the general
list of the amplifier layout with those numerals substituted.  The register has
`3 * (2 + (2 + (1 + 1))) + 1 = 19` wires. -/
private def shiRlPc221 : List (ℕ × ℕ) :=
  [(2, 0), (2, 2), (1, 2 + 3 * 2), (1, 2 + 3 * 2 + 1), (2, 2 + 3 * 2 + 1 + 1), (2, 2 + 2),
   (1, 2 * 2 + 3 * 2 + 1 + 1), (1, 2 * 2 + 3 * 2 + 2 * 1 + 1),
   (2, 2 * 2 + 3 * 2 + 2 * 1 + 2), (2, 2 + 2 * 2), (1, 3 * 2 + 3 * 2 + 2 * 1 + 2),
   (1, 3 * 2 + 3 * 2 + 3 * 1 + 2), (1, 3 * 2 + 3 * 2 + 3 * 1 + 3)]

private def shiRlSt (w : ℕ) : ∀ k : Fin 6, List (shiRlGam k)
  | ⟨0, _⟩ => List.replicate w shiRlGv.mv
  | ⟨1, _⟩ => shiRlPkL shiRlPc221
  | ⟨2, _⟩ => shiRlPkB shiRlPc221
  | _ => []

private theorem shiRlNd :
    ([shiRlKv, shiRlKl, shiRlKb, shiRlKd, shiRlKu, shiRlKr] : List (Fin 6)).Nodup := by decide

private theorem shiRlVL : shiRlKv ≠ shiRlKl := by decide
private theorem shiRlVB : shiRlKv ≠ shiRlKb := by decide
private theorem shiRlVD : shiRlKv ≠ shiRlKd := by decide
private theorem shiRlVU : shiRlKv ≠ shiRlKu := by decide
private theorem shiRlVR : shiRlKv ≠ shiRlKr := by decide
private theorem shiRlLB : shiRlKl ≠ shiRlKb := by decide
private theorem shiRlLD : shiRlKl ≠ shiRlKd := by decide
private theorem shiRlLU : shiRlKl ≠ shiRlKu := by decide
private theorem shiRlLR : shiRlKl ≠ shiRlKr := by decide
private theorem shiRlBD : shiRlKb ≠ shiRlKd := by decide
private theorem shiRlBU : shiRlKb ≠ shiRlKu := by decide
private theorem shiRlBR : shiRlKb ≠ shiRlKr := by decide
private theorem shiRlDU : shiRlKd ≠ shiRlKu := by decide
private theorem shiRlDR : shiRlKd ≠ shiRlKr := by decide
private theorem shiRlUR : shiRlKu ≠ shiRlKr := by decide

private theorem shiRlMl1 : shiRlM shiRlLam.l1
    = Turing.TM2.Stmt.pop shiRlKl shiRlFL (Turing.TM2.Stmt.branch shiRlGL
        (Turing.TM2.Stmt.pop shiRlKv shiRlFV (Turing.TM2.Stmt.branch shiRlGS
          (Turing.TM2.Stmt.push shiRlKd shiRlMD
            (Turing.TM2.Stmt.goto (fun _ => shiRlLam.l1)))
          (Turing.TM2.Stmt.goto (fun _ => shiRlLam.lf))))
        (Turing.TM2.Stmt.goto (fun _ => shiRlLam.la))) := rfl

private theorem shiRlMla : shiRlM shiRlLam.la
    = Turing.TM2.Stmt.pop shiRlKd shiRlFD (Turing.TM2.Stmt.branch shiRlGS
        (Turing.TM2.Stmt.push shiRlKr shiRlHD
          (Turing.TM2.Stmt.goto (fun _ => shiRlLam.la)))
        (Turing.TM2.Stmt.goto (fun _ => shiRlLam.la2))) := rfl

private theorem shiRlMla2 : shiRlM shiRlLam.la2
    = Turing.TM2.Stmt.pop shiRlKb shiRlFB (Turing.TM2.Stmt.branch shiRlGB
        (Turing.TM2.Stmt.push shiRlKr shiRlHP
          (Turing.TM2.Stmt.goto (fun _ => shiRlLam.la2)))
        (Turing.TM2.Stmt.goto (fun _ => shiRlLam.l1))) := rfl

private theorem shiRlMlf : shiRlM shiRlLam.lf
    = Turing.TM2.Stmt.pop shiRlKb shiRlFB (Turing.TM2.Stmt.branch shiRlGB
        (Turing.TM2.Stmt.push shiRlKu shiRlHQ
          (Turing.TM2.Stmt.goto (fun _ => shiRlLam.lf)))
        (Turing.TM2.Stmt.goto (fun _ => shiRlLam.lo))) := rfl

private theorem shiRlMlo : shiRlM shiRlLam.lo
    = Turing.TM2.Stmt.pop shiRlKd shiRlFD (Turing.TM2.Stmt.branch shiRlGS
        (Turing.TM2.Stmt.push shiRlKu shiRlHO
          (Turing.TM2.Stmt.goto (fun _ => shiRlLam.lo)))
        (Turing.TM2.Stmt.goto (fun _ => shiRlLam.lend))) := rfl

private theorem shiRlLmT : ∀ w : shiRlSig, shiRlGL (shiRlFL w (some shiRlGl.ml)) = true := by
  intro w
  rfl

private theorem shiRlLdF : ∀ w : shiRlSig, shiRlGL (shiRlFL w (some shiRlGl.dl)) = false := by
  intro w
  rfl

private theorem shiRlVsT : ∀ (w : shiRlSig) (y : shiRlGv),
    shiRlGS (shiRlFV w (some y)) = true := by
  intro w y
  rfl

private theorem shiRlVnF : ∀ w : shiRlSig, shiRlGS (shiRlFV w none) = false := by
  intro w
  rfl

private theorem shiRlMDc : ∀ w : shiRlSig, shiRlMD w = shiRlGd.md1 := by
  intro w
  rfl

private theorem shiRlDsT : ∀ (w : shiRlSig) (y : shiRlGd),
    shiRlGS (shiRlFD w (some y)) = true := by
  intro w y
  rfl

private theorem shiRlDnF : ∀ w : shiRlSig, shiRlGS (shiRlFD w none) = false := by
  intro w
  rfl

/-- Value recovery on `kd`. -/
private theorem shiRlDvL : ∀ (w : shiRlSig) (y : shiRlGd),
    shiRlHD (shiRlFD w (some y)) = shiRlED y := by
  intro w y
  cases y
  rfl

private theorem shiRlBmT : ∀ w : shiRlSig, shiRlGB (shiRlFB w (some shiRlGb.mb)) = true := by
  intro w
  rfl

private theorem shiRlBdF : ∀ w : shiRlSig, shiRlGB (shiRlFB w (some shiRlGb.db)) = false := by
  intro w
  rfl

/-- Value recovery on `kb` into the discard stack: `shiRlEP` is an INJECTION of the two-symbol
`kb` alphabet into the two-symbol `kr` alphabet, so this law cannot be met by a constant. -/
private theorem shiRlPvL : ∀ (w : shiRlSig) (y : shiRlGb),
    shiRlHP (shiRlFB w (some y)) = shiRlEP y := by
  intro w y
  cases y
  all_goals rfl

private theorem shiRlQvL : ∀ (w : shiRlSig) (y : shiRlGb),
    shiRlHQ (shiRlFB w (some y)) = shiRlEQ y := by
  intro w y
  cases y
  all_goals rfl

private theorem shiRlOvL : ∀ (w : shiRlSig) (y : shiRlGd),
    shiRlHO (shiRlFD w (some y)) = shiRlEO y := by
  intro w y
  cases y
  rfl

private theorem shiRlPkLc : ∀ (a b : ℕ) (t : List (ℕ × ℕ)),
    shiRlPkL ((a, b) :: t) = List.replicate a shiRlGl.ml ++ shiRlGl.dl :: shiRlPkL t := by
  intro a b t
  first
    | rfl
    | simp [shiRlPkL]

private theorem shiRlPkBc : ∀ (a b : ℕ) (t : List (ℕ × ℕ)),
    shiRlPkB ((a, b) :: t) = List.replicate b shiRlGb.mb ++ shiRlGb.db :: shiRlPkB t := by
  intro a b t
  first
    | rfl
    | simp [shiRlPkB]

private theorem shiRlSum : (shiRlPc221.map Prod.fst).sum = 19 := by
  first
    | rfl
    | decide
    | simp [shiRlPc221]

private theorem shiRlPcEq : shiRlPc221
    = [(2, 0), (2, 2), (1, 2 + 3 * 2), (1, 2 + 3 * 2 + 1), (2, 2 + 3 * 2 + 1 + 1), (2, 2 + 2),
       (1, 2 * 2 + 3 * 2 + 1 + 1), (1, 2 * 2 + 3 * 2 + 2 * 1 + 1),
       (2, 2 * 2 + 3 * 2 + 2 * 1 + 2), (2, 2 + 2 * 2), (1, 3 * 2 + 3 * 2 + 2 * 1 + 2),
       (1, 3 * 2 + 3 * 2 + 3 * 1 + 2), (1, 3 * 2 + 3 * 2 + 3 * 1 + 3)] := rfl
/-! ### The witness numerals

Raw wires `4` and `8` land in DIFFERENT pieces of the thirteen: `4` is copy-1 ancilla, found
in piece 3 `(1, 8)` after two advances, and `8` is copy-2 witness, found in piece 6 `(2, 4)`
after five advances.  So the two residual heights below are produced by descents of different
DEPTH, which is exactly what a recursion that failed to track the descent could not do.

At `4`: the tail after the found piece has ten pieces, of lengths summing (with delimiters) to
`24`, and the found piece leaves its own delimiter, so `R1 = 1 + 24 = 25` out of the stack's
own `32`; the base tail sums to `129` out of `142`.
At `8`: the tail has seven pieces, `16` length symbols, and the found piece leaves one unread
mark plus its delimiter, so `R1 = 2 + 16 = 18`; the base tail is `103`. -/

private theorem shiRlR1v4 : shiRlR1 shiRlPc221 4 = 25 := by
  first
    | rfl
    | decide
    | simp [shiRlR1, shiRlPc221]

private theorem shiRlR2v4 : shiRlR2 shiRlPc221 4 = 129 := by
  first
    | rfl
    | decide
    | simp [shiRlR2, shiRlPc221]

private theorem shiRlR1v8 : shiRlR1 shiRlPc221 8 = 18 := by
  first
    | rfl
    | decide
    | simp [shiRlR1, shiRlPc221]

private theorem shiRlR2v8 : shiRlR2 shiRlPc221 8 = 103 := by
  first
    | rfl
    | decide
    | simp [shiRlR2, shiRlPc221]

private theorem shiRlDv4 : shiRlDd shiRlPc221 4 = 8 := by
  first
    | rfl
    | decide
    | simp [shiRlDd, shiRlPc221]

private theorem shiRlDv8 : shiRlDd shiRlPc221 8 = 4 := by
  first
    | rfl
    | decide
    | simp [shiRlDd, shiRlPc221]

private theorem shiRlPLlen32 : (shiRlPkL shiRlPc221).length = 32 := by
  first
    | rfl
    | decide
    | simp [shiRlPkL, shiRlPc221]

private theorem shiRlPBlen142 : (shiRlPkB shiRlPc221).length = 142 := by
  first
    | rfl
    | decide
    | simp [shiRlPkB, shiRlPc221]

private theorem shiRlPcLen : shiRlPc221.length = 13 := by
  first
    | rfl
    | decide
    | simp [shiRlPc221]
private theorem shiRlRun (D C : List (ℕ × ℕ) → ℕ → ℕ)
    (hDc : ∀ (a b : ℕ) (t : List (ℕ × ℕ)) (w : ℕ),
      D ((a, b) :: t) w = if w < a then b + w else D t (w - a))
    (hCc : ∀ (a b : ℕ) (t : List (ℕ × ℕ)) (w : ℕ),
      C ((a, b) :: t) w = if w < a then 2 * w + b + 3 else 2 * a + b + 3 + C t (w - a))
    (w : ℕ) (hw : w < 19) :
    ∃ (v' : shiRlSig) (T : ∀ k, List (shiRlGam k)),
      (fun cf : Option (Turing.TM2.Cfg shiRlGam shiRlLam shiRlSig) =>
          cf.bind (Turing.TM2.step shiRlM))^[C shiRlPc221 w]
          (some { l := some shiRlLam.l1, var := shiRlSig.nil, stk := shiRlSt w })
        = some { l := some shiRlLam.lend, var := v', stk := T }
      ∧ T shiRlKu = List.replicate (D shiRlPc221 w) shiRlGu.m
      ∧ T shiRlKv = []
      ∧ T shiRlKd = []
      ∧ (T shiRlKl).length = shiRlR1 shiRlPc221 w
      ∧ (T shiRlKb).length = shiRlR2 shiRlPc221 w := by
  have hlt : w < (shiRlPc221.map Prod.fst).sum := by
    rw [shiRlSum]
    exact hw
  have hwalk := shiRl_walk (M := shiRlM) (kv := shiRlKv) (kl := shiRlKl) (kb := shiRlKb)
    (kd := shiRlKd) (ku := shiRlKu) (kr := shiRlKr)
    (hvl := shiRlVL) (hvb := shiRlVB) (hvd := shiRlVD) (hvu := shiRlVU) (hvr := shiRlVR)
    (hlb := shiRlLB) (hld := shiRlLD) (hlu := shiRlLU) (hlr := shiRlLR)
    (hbd := shiRlBD) (hbu := shiRlBU) (hbr := shiRlBR)
    (hdu := shiRlDU) (hdr := shiRlDR) (hur := shiRlUR)
    (l1 := shiRlLam.l1) (la := shiRlLam.la) (la2 := shiRlLam.la2) (lf := shiRlLam.lf)
    (lo := shiRlLam.lo) (lend := shiRlLam.lend)
    (fL := shiRlFL) (gL := shiRlGL) (fV := shiRlFV) (gV := shiRlGS) (md := shiRlMD)
    (fD := shiRlFD) (gD := shiRlGS) (hDp := shiRlHD)
    (fB := shiRlFB) (gB := shiRlGB) (hPp := shiRlHP) (hQp := shiRlHQ)
    (fO := shiRlFD) (gO := shiRlGS) (hOp := shiRlHO)
    (eD := shiRlED) (eP := shiRlEP) (eQ := shiRlEQ) (eO := shiRlEO)
    (hM1 := shiRlMl1) (hMa := shiRlMla) (hMa2 := shiRlMla2) (hMf := shiRlMlf)
    (hMo := shiRlMlo)
    (mv := shiRlGv.mv) (ml := shiRlGl.ml) (dl := shiRlGl.dl) (mb := shiRlGb.mb)
    (db := shiRlGb.db) (mdc := shiRlGd.md1) (m := shiRlGu.m)
    (hLm := shiRlLmT) (hLd := shiRlLdF) (hVs := shiRlVsT) (hVn := shiRlVnF)
    (hmd := shiRlMDc) (hDs := shiRlDsT) (hDn := shiRlDnF) (hDv := shiRlDvL)
    (hBm := shiRlBmT) (hBd := shiRlBdF) (hPv := shiRlPvL) (hQv := shiRlQvL)
    (hOs := shiRlDsT) (hOn := shiRlDnF) (hOv := shiRlOvL)
    (hmQ := rfl) (hmO := rfl) (D := D) (C := C) (hDc := hDc) (hCc := hCc)
    (PL := shiRlPkL) (PB := shiRlPkB) (hPLc := shiRlPkLc) (hPBc := shiRlPkBc)
    (R1 := shiRlR1) (R2 := shiRlR2) (hR1c := shiRlR1c) (hR2c := shiRlR2c)
  obtain ⟨v', T, h1, h2, h3, h4, h5, h6, _⟩ :=
    hwalk shiRlPc221 w shiRlSig.nil (shiRlSt w) hlt rfl rfl rfl rfl
  refine ⟨v', T, h1, ?_, h3, h4, ?_, ?_⟩
  · have hu : shiRlSt w shiRlKu = [] := rfl
    rw [h2, hu]
    exact List.append_nil _
  · have h5' : (T shiRlKl).length = shiRlR1 shiRlPc221 w + 0 := h5
    omega
  · have h6' : (T shiRlKb).length = shiRlR2 shiRlPc221 w + 0 := h6
    omega
/-! ### The public statement

Six things, all under one existential exhibiting the two RESIDUAL-LENGTH recursions `R1` and
`R2`, so that nothing is asserted about functions that might not exist:

1. the two defining descents, `R1 [] w = R2 [] w = 0` and the relative-offset step -- the SAME
   descent WIRE-2's index `D` and cost `C` take, so `R1` and `R2` are read off the same
   thirteen-piece walk with no extra data;
2. the GENERIC block, for any list of pieces on any alphabet, now with the two residual
   heights as EQUATIONS `(T kl).length = R1 ps w` and `(T kb).length = R2 ps w` rather than
   bounds -- the one thing an EXACT-cost composition needs, since a reload pass over the
   residuals then costs a function of `(ps, w)` alone;
3. the two ceilings `R1 ps w <= (PL ps).length` and `R2 ps w <= (PB ps).length`, from which
   WIRE-2's original bounds `(T kl).length <= (S kl).length` follow, also asserted;
4. a NON-VACUITY witness, asserted unconditionally: the same concrete six-stack machine and
   the same thirteen pieces at `n = wit = 2`, `anc = 1`, run at TWO raw wires that lie in
   DIFFERENT pieces -- `4` (copy-1 ancilla, piece 3, two advances) and `8` (copy-2 witness,
   piece 6, five advances) -- with the residual heights checked against LITERAL numerals
   `25`, `129` and `18`, `103` against the stacks' own heights `32` and `142`.  Descents of
   different depth give different residuals, so the numerals test that the recursions track
   the descent rather than coinciding at one point. -/
theorem solution :
    ∃ R1 R2 : List (ℕ × ℕ) → ℕ → ℕ,
    (∀ w : ℕ, R1 [] w = 0)
    ∧ (∀ (a b : ℕ) (t : List (ℕ × ℕ)) (w : ℕ),
        R1 ((a, b) :: t) w
          = if w < a then (a - w) + (t.map (fun p => p.1 + 1)).sum else R1 t (w - a))
    ∧ (∀ w : ℕ, R2 [] w = 0)
    ∧ (∀ (a b : ℕ) (t : List (ℕ × ℕ)) (w : ℕ),
        R2 ((a, b) :: t) w
          = if w < a then (t.map (fun p => p.2 + 1)).sum else R2 t (w - a))
    ∧
    (∀ {K : Type} [DecidableEq K] {Gam : K → Type} {Lam sig : Type}
    (M : Lam → Stmt Gam Lam sig) {kv kl kb kd ku kr : K}
    (hvl : kv ≠ kl) (hvb : kv ≠ kb) (hvd : kv ≠ kd) (hvu : kv ≠ ku) (hvr : kv ≠ kr)
    (hlb : kl ≠ kb) (hld : kl ≠ kd) (hlu : kl ≠ ku) (hlr : kl ≠ kr)
    (hbd : kb ≠ kd) (hbu : kb ≠ ku) (hbr : kb ≠ kr)
    (hdu : kd ≠ ku) (hdr : kd ≠ kr) (hur : ku ≠ kr)
    {l1 la la2 lf lo lend : Lam}
    {fL : sig → Option (Gam kl) → sig} {gL : sig → Bool}
    {fV : sig → Option (Gam kv) → sig} {gV : sig → Bool}
    {md : sig → Gam kd}
    {fD : sig → Option (Gam kd) → sig} {gD : sig → Bool} {hDp : sig → Gam kr}
    {fB : sig → Option (Gam kb) → sig} {gB : sig → Bool} {hPp : sig → Gam kr}
    {hQp : sig → Gam ku}
    {fO : sig → Option (Gam kd) → sig} {gO : sig → Bool} {hOp : sig → Gam ku}
    {eD : Gam kd → Gam kr} {eP : Gam kb → Gam kr}
    {eQ : Gam kb → Gam ku} {eO : Gam kd → Gam ku}
    (hM1 : M l1 = Stmt.pop kl fL (Stmt.branch gL
             (Stmt.pop kv fV (Stmt.branch gV
               (Stmt.push kd md (Stmt.goto (fun _ => l1)))
               (Stmt.goto (fun _ => lf))))
             (Stmt.goto (fun _ => la))))
    (hMa : M la = Stmt.pop kd fD (Stmt.branch gD
             (Stmt.push kr hDp (Stmt.goto (fun _ => la)))
             (Stmt.goto (fun _ => la2))))
    (hMa2 : M la2 = Stmt.pop kb fB (Stmt.branch gB
             (Stmt.push kr hPp (Stmt.goto (fun _ => la2)))
             (Stmt.goto (fun _ => l1))))
    (hMf : M lf = Stmt.pop kb fB (Stmt.branch gB
             (Stmt.push ku hQp (Stmt.goto (fun _ => lf)))
             (Stmt.goto (fun _ => lo))))
    (hMo : M lo = Stmt.pop kd fO (Stmt.branch gO
             (Stmt.push ku hOp (Stmt.goto (fun _ => lo)))
             (Stmt.goto (fun _ => lend))))
    {mv : Gam kv} {ml dl : Gam kl} {mb db : Gam kb} {mdc : Gam kd} {m : Gam ku}
    (hLm : ∀ w : sig, gL (fL w (some ml)) = true)
    (hLd : ∀ w : sig, gL (fL w (some dl)) = false)
    (hVs : ∀ (w : sig) (y : Gam kv), gV (fV w (some y)) = true)
    (hVn : ∀ w : sig, gV (fV w none) = false)
    (hmd : ∀ w : sig, md w = mdc)
    (hDs : ∀ (w : sig) (y : Gam kd), gD (fD w (some y)) = true)
    (hDn : ∀ w : sig, gD (fD w none) = false)
    (hDv : ∀ (w : sig) (y : Gam kd), hDp (fD w (some y)) = eD y)
    (hBm : ∀ w : sig, gB (fB w (some mb)) = true)
    (hBd : ∀ w : sig, gB (fB w (some db)) = false)
    (hPv : ∀ (w : sig) (y : Gam kb), hPp (fB w (some y)) = eP y)
    (hQv : ∀ (w : sig) (y : Gam kb), hQp (fB w (some y)) = eQ y)
    (hOs : ∀ (w : sig) (y : Gam kd), gO (fO w (some y)) = true)
    (hOn : ∀ w : sig, gO (fO w none) = false)
    (hOv : ∀ (w : sig) (y : Gam kd), hOp (fO w (some y)) = eO y)
    (hmQ : eQ mb = m) (hmO : eO mdc = m)
    (D C : List (ℕ × ℕ) → ℕ → ℕ)
    (hDc : ∀ (a b : ℕ) (t : List (ℕ × ℕ)) (w : ℕ),
      D ((a, b) :: t) w = if w < a then b + w else D t (w - a))
    (hCc : ∀ (a b : ℕ) (t : List (ℕ × ℕ)) (w : ℕ),
      C ((a, b) :: t) w = if w < a then 2 * w + b + 3 else 2 * a + b + 3 + C t (w - a))
    (PL : List (ℕ × ℕ) → List (Gam kl)) (PB : List (ℕ × ℕ) → List (Gam kb))
    (hPLc : ∀ (a b : ℕ) (t : List (ℕ × ℕ)),
      PL ((a, b) :: t) = List.replicate a ml ++ dl :: PL t)
    (hPBc : ∀ (a b : ℕ) (t : List (ℕ × ℕ)),
      PB ((a, b) :: t) = List.replicate b mb ++ db :: PB t)
    (hPL0 : PL ([] : List (ℕ × ℕ)) = [])
    (hPB0 : PB ([] : List (ℕ × ℕ)) = []),
    ∀ (ps : List (ℕ × ℕ)) (w : ℕ) (v : sig) (S : ∀ k, List (Gam k)),
      w < (ps.map Prod.fst).sum →
      S kv = List.replicate w mv → S kl = PL ps → S kb = PB ps → S kd = [] →
      ∃ (v' : sig) (T : ∀ k, List (Gam k)),
        (fun cf : Option (Cfg Gam Lam sig) => cf.bind (step M))^[C ps w]
            (some { l := some l1, var := v, stk := S })
          = some { l := some lend, var := v', stk := T }
        ∧ T ku = List.replicate (D ps w) m ++ S ku
        ∧ T kv = []
        ∧ T kd = []
        ∧ (T kl).length = R1 ps w
        ∧ (T kb).length = R2 ps w
        ∧ R1 ps w ≤ (PL ps).length
        ∧ R2 ps w ≤ (PB ps).length
        ∧ (T kl).length ≤ (S kl).length
        ∧ (T kb).length ≤ (S kb).length
        ∧ (∀ k, k ≠ kv → k ≠ kl → k ≠ kb → k ≠ kd → k ≠ ku → k ≠ kr → T k = S k))
    ∧ (∃ (Gam : Fin 6 → Type) (Lam sig : Type)
        (M : Lam → Turing.TM2.Stmt Gam Lam sig) (kv kl kb kd ku kr : Fin 6) (l1 lend : Lam)
        (mv : Gam kv) (ml dl : Gam kl) (mb db : Gam kb) (m : Gam ku)
        (PL : List (ℕ × ℕ) → List (Gam kl)) (PB : List (ℕ × ℕ) → List (Gam kb))
        (D C : List (ℕ × ℕ) → ℕ → ℕ)
        (v : sig) (S : ℕ → ∀ k, List (Gam k)) (pcs : List (ℕ × ℕ))
        (T4 T8 : ∀ k, List (Gam k)) (v4 v8 : sig),
        ([kv, kl, kb, kd, ku, kr] : List (Fin 6)).Nodup
        ∧ ml ≠ dl
        ∧ mb ≠ db
        ∧ (∀ (a b : ℕ) (t : List (ℕ × ℕ)),
            PL ((a, b) :: t) = List.replicate a ml ++ dl :: PL t)
        ∧ (∀ (a b : ℕ) (t : List (ℕ × ℕ)),
            PB ((a, b) :: t) = List.replicate b mb ++ db :: PB t)
        ∧ PL ([] : List (ℕ × ℕ)) = []
        ∧ PB ([] : List (ℕ × ℕ)) = []
        ∧ (∀ (a b : ℕ) (t : List (ℕ × ℕ)) (w : ℕ),
            D ((a, b) :: t) w = if w < a then b + w else D t (w - a))
        ∧ (∀ (a b : ℕ) (t : List (ℕ × ℕ)) (w : ℕ),
            C ((a, b) :: t) w
              = if w < a then 2 * w + b + 3 else 2 * a + b + 3 + C t (w - a))
        ∧ pcs = [(2, 0), (2, 2), (1, 2 + 3 * 2), (1, 2 + 3 * 2 + 1), (2, 2 + 3 * 2 + 1 + 1),
                 (2, 2 + 2), (1, 2 * 2 + 3 * 2 + 1 + 1), (1, 2 * 2 + 3 * 2 + 2 * 1 + 1),
                 (2, 2 * 2 + 3 * 2 + 2 * 1 + 2), (2, 2 + 2 * 2),
                 (1, 3 * 2 + 3 * 2 + 2 * 1 + 2), (1, 3 * 2 + 3 * 2 + 3 * 1 + 2),
                 (1, 3 * 2 + 3 * 2 + 3 * 1 + 3)]
        ∧ pcs.length = 13
        ∧ (PL pcs).length = 32
        ∧ (PB pcs).length = 142
        ∧ (∀ w : ℕ, S w kv = List.replicate w mv ∧ S w kl = PL pcs ∧ S w kb = PB pcs
            ∧ S w kd = [] ∧ S w ku = [])
        ∧ D pcs 4 = 8
        ∧ D pcs 8 = 4
        ∧ R1 pcs 4 = 25
        ∧ R2 pcs 4 = 129
        ∧ R1 pcs 8 = 18
        ∧ R2 pcs 8 = 103
        ∧ (fun cf : Option (Turing.TM2.Cfg Gam Lam sig) =>
            cf.bind (Turing.TM2.step M))^[C pcs 4]
            (some { l := some l1, var := v, stk := S 4 })
          = some { l := some lend, var := v4, stk := T4 }
        ∧ T4 ku = List.replicate 8 m
        ∧ (T4 kl).length = 25
        ∧ (T4 kb).length = 129
        ∧ (fun cf : Option (Turing.TM2.Cfg Gam Lam sig) =>
            cf.bind (Turing.TM2.step M))^[C pcs 8]
            (some { l := some l1, var := v, stk := S 8 })
          = some { l := some lend, var := v8, stk := T8 }
        ∧ T8 ku = List.replicate 4 m
        ∧ (T8 kl).length = 18
        ∧ (T8 kb).length = 103) := by
  have hmld : shiRlGl.ml ≠ shiRlGl.dl := by
    intro h
    exact shiRlGl.noConfusion h
  have hmbd : shiRlGb.mb ≠ shiRlGb.db := by
    intro h
    exact shiRlGb.noConfusion h
  obtain ⟨u4, T4, r4, o4, _, _, l4, b4⟩ :=
    shiRlRun shiRlDd shiRlCc shiRlDdc shiRlCcc 4 (by omega)
  obtain ⟨u8, T8, r8, o8, _, _, l8, b8⟩ :=
    shiRlRun shiRlDd shiRlCc shiRlDdc shiRlCcc 8 (by omega)
  rw [shiRlDv4] at o4
  rw [shiRlDv8] at o8
  refine ⟨shiRlR1, shiRlR2, shiRlR10, shiRlR1c, shiRlR20, shiRlR2c,
    @shiRl_walk_exact, ?_⟩
  exact ⟨shiRlGam, shiRlLam, shiRlSig, shiRlM, shiRlKv, shiRlKl, shiRlKb, shiRlKd,
    shiRlKu, shiRlKr, shiRlLam.l1, shiRlLam.lend, shiRlGv.mv, shiRlGl.ml, shiRlGl.dl,
    shiRlGb.mb, shiRlGb.db, shiRlGu.m, shiRlPkL, shiRlPkB, shiRlDd, shiRlCc,
    shiRlSig.nil, shiRlSt, shiRlPc221, T4, T8, u4, u8, shiRlNd, hmld, hmbd, shiRlPkLc,
    shiRlPkBc, rfl, rfl, shiRlDdc, shiRlCcc, shiRlPcEq, shiRlPcLen, shiRlPLlen32,
    shiRlPBlen142, fun w => ⟨rfl, rfl, rfl, rfl, rfl⟩, shiRlDv4, shiRlDv8, shiRlR1v4,
    shiRlR2v4, shiRlR1v8, shiRlR2v8, r4, o4, l4.trans shiRlR1v4, b4.trans shiRlR2v4,
    r8, o8, l8.trans shiRlR1v8, b8.trans shiRlR2v8⟩
