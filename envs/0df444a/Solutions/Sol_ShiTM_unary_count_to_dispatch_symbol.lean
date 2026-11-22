-- Prove2me | solution 1 for ShiTM.unary_count_to_dispatch_symbol
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-16T10:41:23.318329+00:00
-- url     : https://prove2.me/submissions/126a4c88-5c96-4fc1-bacd-717f14947cb5

/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import Mathlib.Computability.TuringMachine.Computable

set_option autoImplicit false

open Turing Turing.TM2

/-!
# Turning a parsed unary count into a single dispatchable symbol (`TM2`)

`ShiTM.encNat_parser_block` leaves a parsed value as a UNARY COUNT `List.replicate c mark`;
`ShiTM.encInstr_cnot_shift_block` dispatches with `pop ktag; goto (flab ...)`, needing ONE
symbol whose identity selects a label.  This file is the missing converter block.

## The statement is BOUNDED, and that is the honest form

`sig`, each `Gam k` and `Lam` are fixed, and a `Stmt` tree is a FINITE program, so a block can
mention only finitely many tag symbols: no block maps `c` to "the symbol encoding `c`" for
unbounded `c`.  Hence a bound `B`, a caller-supplied family `tagOf : ℕ → Gam ktag` (only its
values on `0, …, B-1` are used), and `c < B`.  Dispatch needs exactly this: the five tags
`h, s, t, x, cnot` are `c ∈ {0,1,2,3,4}`, i.e. `B = 5`.

## Mechanism: counter-consuming label chain (design (a))

At link `lab i` the machine runs ONE statement tree

    pop kmark fpop (branch gmark (goto fun _ => lab (i+1))
                                 (push ktag (fun _ => tagOf i) (goto fun _ => lnext)))

so a `mark` continues to `lab (i+1)` — the counter lives in the LABEL INDEX — and the first
non-`mark` cell (or the empty stack) ends the chain, pushing `tagOf i` and going to `lnext`.
Cost `c + 1` steps, `B` label equations.

Design (b), a `Fin B` counter inside `sig` with one label, is rejected: it needs a global law
`cnt (fpop w (some mark)) = cnt w + 1` on ALL of `sig` (UNSATISFIABLE unguarded for finite
`sig`) plus an initialisation `cnt v = 0`, forcing the composer to fix a `sig` LAYOUT before
writing any block and coupling this block to every other block touching `sig`.  Design (a)
constrains only the program TEXT of `M` — the hypothesis shape every accepted `ShiTM` block
already uses — and assumes NOTHING about `sig`.  Both cost `c + 1` steps.

## Termination: one hypothesis, both conventions

`hstop : ∀ w, gmark (fpop w tl.head?) = false` says the cell past the marks is not a mark.
`tl = sep :: _` is the TERMINATED convention; `tl = []` gives `tl.head? = none`, the count
delimited by the STACK BOTTOM (what `encNat_parser_block` leaves on an initially empty target
stack).  Phrasing with `head?` covers both at once.
-/

/-! ### Bureaucratic lemmas -/

/-- Two updates at the same key collapse to the outer one. -/
private theorem shiCv_update_idem {K : Type} [DecidableEq K] {Γ : K → Type}
    (k : K) (S : ∀ j, List (Γ j)) (a b : List (Γ k)) :
    Function.update (Function.update S k a) k b = Function.update S k b := by
  funext j
  by_cases h : j = k
  · subst h
    simp only [Function.update_self]
  · simp only [Function.update_of_ne h]

/-! ### One-`stepAux`-node lemmas (each `rfl` modulo the popped-cell rewrite) -/

private theorem shiCv_aux_pop_at {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (k : K) (f : σ → Option (Γ k) → σ) (Q : Stmt Γ Λ σ) (v : σ) (S : ∀ j, List (Γ j))
    (t : List (Γ k)) (hS : S k = t) :
    stepAux (Stmt.pop k f Q) v S = stepAux Q (f v t.head?) (Function.update S k t.tail) := by
  have h : stepAux (Stmt.pop k f Q) v S
      = stepAux Q (f v (S k).head?) (Function.update S k (S k).tail) := rfl
  rw [h, hS]

private theorem shiCv_aux_branch_true {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (g : σ → Bool) (Q₁ Q₂ : Stmt Γ Λ σ) (v : σ) (S : ∀ j, List (Γ j)) (hg : g v = true) :
    stepAux (Stmt.branch g Q₁ Q₂) v S = stepAux Q₁ v S := by
  have h : stepAux (Stmt.branch g Q₁ Q₂) v S
      = cond (g v) (stepAux Q₁ v S) (stepAux Q₂ v S) := rfl
  rw [h, hg]
  all_goals rfl

private theorem shiCv_aux_branch_false {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (g : σ → Bool) (Q₁ Q₂ : Stmt Γ Λ σ) (v : σ) (S : ∀ j, List (Γ j)) (hg : g v = false) :
    stepAux (Stmt.branch g Q₁ Q₂) v S = stepAux Q₂ v S := by
  have h : stepAux (Stmt.branch g Q₁ Q₂) v S
      = cond (g v) (stepAux Q₁ v S) (stepAux Q₂ v S) := rfl
  rw [h, hg]
  all_goals rfl

private theorem shiCv_aux_push {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (k : K) (f : σ → Γ k) (Q : Stmt Γ Λ σ) (v : σ) (S : ∀ j, List (Γ j)) :
    stepAux (Stmt.push k f Q) v S = stepAux Q v (Function.update S k (f v :: S k)) := rfl

private theorem shiCv_aux_goto {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (fl : σ → Λ) (v : σ) (S : ∀ j, List (Γ j)) :
    stepAux (Stmt.goto fl) v S = { l := some (fl v), var := v, stk := S } := rfl

/-! ### The two one-`step` transitions of the chain -/

/-- CONTINUE: the popped cell reads as a `mark`, so control moves to the next link `lcont`
and nothing is pushed.  One step (the whole `pop/branch/goto` tree runs in one `step`). -/
private theorem shiCv_step_cont {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (M : Λ → Stmt Γ Λ σ) {km kt : K} {fpop : σ → Option (Γ km) → σ} {gmark : σ → Bool}
    (l0 lcont lnext : Λ) (tg : Γ kt)
    (hMj : M l0 = Stmt.pop km fpop
            (Stmt.branch gmark
              (Stmt.goto (fun _ => lcont))
              (Stmt.push kt (fun _ => tg) (Stmt.goto (fun _ => lnext)))))
    (v : σ) (S : ∀ k, List (Γ k)) (mark : Γ km) (rest : List (Γ km))
    (hS : S km = mark :: rest) (hg : gmark (fpop v (some mark)) = true) :
    step M { l := some l0, var := v, stk := S }
      = some { l := some lcont, var := fpop v (some mark),
               stk := Function.update S km rest } := by
  have h0 : step M { l := some l0, var := v, stk := S } = some (stepAux (M l0) v S) := rfl
  have h1 : stepAux (M l0) v S
      = stepAux (Stmt.branch gmark
          (Stmt.goto (fun _ => lcont))
          (Stmt.push kt (fun _ => tg) (Stmt.goto (fun _ => lnext))))
          (fpop v (some mark)) (Function.update S km rest) := by
    rw [hMj, shiCv_aux_pop_at km fpop _ v S (mark :: rest) hS]
    all_goals rfl
  rw [h0, h1, shiCv_aux_branch_true gmark _ _ _ _ hg, shiCv_aux_goto]
  all_goals rfl

/-- STOP: the cell just past the marks (or the stack bottom, `t.head? = none`) does NOT read
as a mark.  It is still consumed — the `pop` node runs before the `branch` node — and the
single tag symbol `tg` is pushed onto `kt`.  One step. -/
private theorem shiCv_step_stop {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (M : Λ → Stmt Γ Λ σ) {km kt : K} (hab : km ≠ kt)
    {fpop : σ → Option (Γ km) → σ} {gmark : σ → Bool}
    (l0 lcont lnext : Λ) (tg : Γ kt)
    (hMj : M l0 = Stmt.pop km fpop
            (Stmt.branch gmark
              (Stmt.goto (fun _ => lcont))
              (Stmt.push kt (fun _ => tg) (Stmt.goto (fun _ => lnext)))))
    (v : σ) (S : ∀ k, List (Γ k)) (t : List (Γ km)) (hS : S km = t)
    (hg : gmark (fpop v t.head?) = false) :
    step M { l := some l0, var := v, stk := S }
      = some { l := some lnext, var := fpop v t.head?,
               stk := Function.update (Function.update S km t.tail) kt (tg :: S kt) } := by
  have h0 : step M { l := some l0, var := v, stk := S } = some (stepAux (M l0) v S) := rfl
  rw [h0, hMj, shiCv_aux_pop_at km fpop _ v S t hS,
    shiCv_aux_branch_false gmark _ _ _ _ hg, shiCv_aux_push, shiCv_aux_goto,
    Function.update_of_ne (Ne.symm hab) t.tail S]
  all_goals rfl

/-! ### The chain induction -/

/-- Running the chain from link `lab j` on a stack `List.replicate n mark ++ tl` takes
exactly `n + 1` steps and lands at `lnext` with `tagOf m`, `m = j + n`, on top of `kt`.
The tag index `m` is a parameter constrained by `m = j + n` rather than the literal term
`j + n`, so that both the base case (`m := j + 0`) and the caller (`j := 0`, `m := c`) close
by definitional unfolding instead of an arithmetic rewrite inside a structure field. -/
private theorem shiCv_chain {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (M : Λ → Stmt Γ Λ σ) {km kt : K} (hab : km ≠ kt)
    {fpop : σ → Option (Γ km) → σ} {gmark : σ → Bool}
    (B : ℕ) (lab : ℕ → Λ) (lnext : Λ) (tagOf : ℕ → Γ kt)
    (hM : ∀ i, i < B → M (lab i) = Stmt.pop km fpop
            (Stmt.branch gmark
              (Stmt.goto (fun _ => lab (i + 1)))
              (Stmt.push kt (fun _ => tagOf i) (Stmt.goto (fun _ => lnext)))))
    (mark : Γ km) (hmark : ∀ w : σ, gmark (fpop w (some mark)) = true)
    (tl : List (Γ km)) (hstop : ∀ w : σ, gmark (fpop w tl.head?) = false) :
    ∀ (n j m : ℕ) (v : σ) (S : ∀ k, List (Γ k)), n + j < B → m = j + n →
      S km = List.replicate n mark ++ tl →
      (fun cf : Option (Cfg Γ Λ σ) => cf.bind (step M))^[n + 1]
          (some { l := some (lab j), var := v, stk := S })
        = some { l := some lnext,
                 var := fpop (List.foldl (fun w y => fpop w (some y)) v
                          (List.replicate n mark)) tl.head?,
                 stk := Function.update (Function.update S km tl.tail) kt
                          (tagOf m :: S kt) } := by
  intro n
  induction n with
  | zero =>
    intro j m v S hjn hm hS
    rw [hm]
    have hS0 : S km = tl := by
      rw [hS, List.replicate_zero, List.nil_append]
    have h1 : step M { l := some (lab j), var := v, stk := S }
        = some { l := some lnext, var := fpop v tl.head?,
                 stk := Function.update (Function.update S km tl.tail) kt
                          (tagOf j :: S kt) } :=
      shiCv_step_stop M hab (lab j) (lab (j + 1)) lnext (tagOf j) (hM j (by omega))
        v S tl hS0 (hstop v)
    have hstepb : (some { l := some (lab j), var := v, stk := S } : Option (Cfg Γ Λ σ)).bind
        (step M)
        = some { l := some lnext, var := fpop v tl.head?,
                 stk := Function.update (Function.update S km tl.tail) kt
                          (tagOf j :: S kt) } := h1
    rw [Function.iterate_succ_apply, hstepb]
    all_goals rfl
  | succ n ih =>
    intro j m v S hjn hm hS
    subst hm
    have hSc : S km = mark :: (List.replicate n mark ++ tl) := by
      rw [hS, List.replicate_succ, List.cons_append]
    have h1 : step M { l := some (lab j), var := v, stk := S }
        = some { l := some (lab (j + 1)), var := fpop v (some mark),
                 stk := Function.update S km (List.replicate n mark ++ tl) } :=
      shiCv_step_cont M (lab j) (lab (j + 1)) lnext (tagOf j) (hM j (by omega))
        v S mark (List.replicate n mark ++ tl) hSc (hmark v)
    have hstepb : (some { l := some (lab j), var := v, stk := S } : Option (Cfg Γ Λ σ)).bind
        (step M)
        = some { l := some (lab (j + 1)), var := fpop v (some mark),
                 stk := Function.update S km (List.replicate n mark ++ tl) } := h1
    have hS1 : (Function.update S km (List.replicate n mark ++ tl)) km
        = List.replicate n mark ++ tl := Function.update_self km _ S
    have h2 := ih (j + 1) (j + 1 + n) (fpop v (some mark))
      (Function.update S km (List.replicate n mark ++ tl)) (by omega) (by omega) hS1
    have hfold : List.foldl (fun w y => fpop w (some y)) v (List.replicate (n + 1) mark)
        = List.foldl (fun w y => fpop w (some y)) (fpop v (some mark))
            (List.replicate n mark) := by
      rw [List.replicate_succ]
      all_goals rfl
    have hidx : j + (n + 1) = j + 1 + n := by omega
    have hupd : Function.update (Function.update
          (Function.update S km (List.replicate n mark ++ tl)) km tl.tail) kt
          (tagOf (j + 1 + n)
            :: (Function.update S km (List.replicate n mark ++ tl)) kt)
        = Function.update (Function.update S km tl.tail) kt
            (tagOf (j + 1 + n) :: S kt) := by
      rw [shiCv_update_idem km S (List.replicate n mark ++ tl) tl.tail,
        Function.update_of_ne (Ne.symm hab) (List.replicate n mark ++ tl) S]
    rw [hidx, hfold, ← hupd, Function.iterate_succ_apply, hstepb]
    exact h2

/-! ### The public statement -/

/-- **Unary count to dispatchable symbol, for an arbitrary `Turing.TM2` machine.**

Let `M` run, at each chain link `lab i` (for `i < B`), the single statement tree

    pop kmark fpop (branch gmark (goto fun _ => lab (i+1))
                                 (push ktag (fun _ => tagOf i) (goto fun _ => lnext)))

and let stack `kmark` hold `List.replicate c mark ++ tl`, where `mark` reads as a mark
(`hmark`) and the cell just past the marks does not (`hstop`, phrased with `tl.head?` so
that `tl = []`, i.e. the stack bottom, is included).  Then for `c < B` the block runs in
EXACTLY `c + 1` steps, consumes the `c` marks and the one delimiter cell, and leaves the
SINGLE symbol `tagOf c` on top of stack `ktag` — so a following `pop ktag; goto (flab …)`
dispatches on `c`.  The final `head?` conclusion is literally what such a `pop` reads.

The bound `B` is unavoidable: `Gam ktag`, `Lam` and the program `M` are fixed, so only
finitely many tags can be emitted; `tagOf` is supplied by the caller and only its values on
`0, …, B-1` are used.  Nothing is assumed about `sig`, and `M` is arbitrary. -/
theorem solution {K : Type} [DecidableEq K] {Gam : K → Type} {Lam sig : Type}
    (M : Lam → Turing.TM2.Stmt Gam Lam sig) {kmark ktag : K} (hab : kmark ≠ ktag)
    {fpop : sig → Option (Gam kmark) → sig} {gmark : sig → Bool}
    (B : ℕ) (lab : ℕ → Lam) (lnext : Lam) (tagOf : ℕ → Gam ktag)
    (hM : ∀ i, i < B → M (lab i) = Turing.TM2.Stmt.pop kmark fpop
            (Turing.TM2.Stmt.branch gmark
              (Turing.TM2.Stmt.goto (fun _ => lab (i + 1)))
              (Turing.TM2.Stmt.push ktag (fun _ => tagOf i)
                (Turing.TM2.Stmt.goto (fun _ => lnext)))))
    (mark : Gam kmark) (hmark : ∀ w : sig, gmark (fpop w (some mark)) = true)
    (tl : List (Gam kmark)) (hstop : ∀ w : sig, gmark (fpop w tl.head?) = false)
    (c : ℕ) (hc : c < B) (v : sig) (S : ∀ k, List (Gam k))
    (hS : S kmark = List.replicate c mark ++ tl) :
    (fun cf : Option (Turing.TM2.Cfg Gam Lam sig) => cf.bind (Turing.TM2.step M))^[c + 1]
        (some { l := some (lab 0), var := v, stk := S })
      = some { l := some lnext,
               var := fpop (List.foldl (fun w y => fpop w (some y)) v
                        (List.replicate c mark)) tl.head?,
               stk := Function.update (Function.update S kmark tl.tail) ktag
                        (tagOf c :: S ktag) }
    ∧ Nonempty (StateTransition.EvalsToInTime (Turing.TM2.step M)
        { l := some (lab 0), var := v, stk := S }
        (some { l := some lnext,
                var := fpop (List.foldl (fun w y => fpop w (some y)) v
                         (List.replicate c mark)) tl.head?,
                stk := Function.update (Function.update S kmark tl.tail) ktag
                         (tagOf c :: S ktag) })
        (c + 1))
    ∧ (Function.update (Function.update S kmark tl.tail) ktag (tagOf c :: S ktag)) kmark
        = tl.tail
    ∧ (Function.update (Function.update S kmark tl.tail) ktag (tagOf c :: S ktag)) ktag
        = tagOf c :: S ktag
    ∧ ((Function.update (Function.update S kmark tl.tail) ktag
        (tagOf c :: S ktag)) ktag).head? = some (tagOf c) := by
  have hkey := shiCv_chain M hab B lab lnext tagOf hM mark hmark tl hstop c 0 c v S
    (by omega) (Nat.zero_add c).symm hS
  have hres : (Function.update (Function.update S kmark tl.tail) ktag
      (tagOf c :: S ktag)) kmark = tl.tail := by
    rw [Function.update_of_ne hab, Function.update_self]
  have htag : (Function.update (Function.update S kmark tl.tail) ktag
      (tagOf c :: S ktag)) ktag = tagOf c :: S ktag := by
    rw [Function.update_self]
  have hhd : ((Function.update (Function.update S kmark tl.tail) ktag
      (tagOf c :: S ktag)) ktag).head? = some (tagOf c) := by
    rw [htag]
    all_goals rfl
  exact ⟨hkey, ⟨⟨c + 1, hkey⟩, le_refl _⟩, hres, htag, hhd⟩

/-! ### Satisfiability witness (the statement is NOT vacuous)

`K = Bool` (`kmark = true`, `ktag = false`), `Gam = fun _ => Fin 5` (five tags, enough for
`h, s, t, x, cnot`), `Lam = ℕ` with `lab i = i` and `lnext = 100`, `sig = Option (Fin 5)`
(the variable just remembers the popped cell), `mark = 0`, delimiter `tl = [1]`, and
`tagOf n = n % 5`.  Every hypothesis of `solution` is discharged by `rfl`/`decide`, for every
`c < 5`, every `v` and the displayed `S`.  Note also `shiCv_tags_injOn`: the tag family is
INJECTIVE on `{0,1,2,3,4}`, so the emitted symbol really can select five distinct labels —
nothing in the statement forces `tagOf` to be injective, but injectivity is satisfiable, and
that is what makes the block useful for dispatch.  The marks are likewise distinguishable
from the delimiter (`0 ≠ 1` in `Fin 5`), as `hmark` and `hstop` together require. -/

private def shiCv_tag (n : ℕ) : Fin 5 := ⟨n % 5, by omega⟩

private theorem shiCv_tags_injOn (i j : ℕ) (hi : i < 5) (hj : j < 5)
    (h : shiCv_tag i = shiCv_tag j) : i = j := by
  have h' : i % 5 = j % 5 := congrArg Fin.val h
  omega

private def shiCv_M (l : ℕ) : Stmt (fun _ : Bool => Fin 5) ℕ (Option (Fin 5)) :=
  Stmt.pop true (fun _ y => y)
    (Stmt.branch (fun w => decide (w = some 0))
      (Stmt.goto (fun _ => l + 1))
      (Stmt.push false (fun _ => shiCv_tag l) (Stmt.goto (fun _ => 100))))

private theorem shiCv_witness (c : ℕ) (hc : c < 5) (v : Option (Fin 5)) : True := by
  have _h := solution (M := shiCv_M) (kmark := true) (ktag := false) (hab := by decide)
    (fpop := fun _ y => y) (gmark := fun w => decide (w = some 0))
    (B := 5) (lab := fun i => i) (lnext := 100) (tagOf := shiCv_tag)
    (hM := fun i _ => rfl) (mark := 0) (hmark := fun _ => rfl)
    (tl := [1]) (hstop := fun _ => rfl) (c := c) (hc := hc) (v := v)
    (S := fun _ => List.replicate c 0 ++ [1]) (hS := rfl)
  trivial
