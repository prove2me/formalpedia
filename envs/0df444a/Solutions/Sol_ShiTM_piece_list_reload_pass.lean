-- Prove2me | solution 1 for ShiTM.piece_list_reload_pass
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-17T23:20:27.263649+00:00
-- url     : https://prove2.me/submissions/ca02a69e-1adc-4bcf-99f2-0fb20adb8d12

/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import Mathlib.Computability.TuringMachine.Computable
import Theorems.Thm_ShiTM_counted_loop_transfers_prefix_with_marks
import Theorems.Thm_ShiTM_copy_loop_transfers_stack

set_option autoImplicit false

open Turing Turing.TM2

/-!
# The PIECE-LIST RELOAD PASS

`ShiTM.piecewise_layout_index_block_and_amplifier_instantiation` (the amplifier's
thirteen-piece wire-index block) has, at its two piece-list stacks `kl` and `kb`, the
PRECONDITION `S kl = PL ps`, `S kb = PB ps` -- two EQUATIONS -- but only the
POSTCONDITION `(T kl).length ≤ (S kl).length`, `(T kb).length ≤ (S kb).length` -- two
LENGTH BOUNDS.  The piece-list material is popped at its `l1` node and banked nowhere
(it goes to the discard stack or to the output), so the equations are not recoverable
from the post-state.  An element-iteration invariant can therefore neither DROP the
`kl`/`kb` clauses (they are the block's own precondition, so the block could not be
re-entered on the next element) nor KEEP them (a length bound does not re-establish an
equation).  This file supplies the missing pass: master copies on `kml`, `kmb` and a
reload that re-establishes the two equations from ANY starting state.

## Why `ShiTM.nondestructive_copy_two_pass` does NOT fit

That theorem is the obvious tool and it is the right two-pass shape, but its master stack
`ka` comes back as `p ++ t`: the SENTINEL `c` that terminates the copied prefix is
CONSUMED (`pop` runs strictly before `branch`, so the stopping symbol is always eaten)
and its `M l2` exit arm is a bare `goto l3`, which gives no opportunity to put the
sentinel back BEFORE the second pass re-pushes `p` on top of it.  Used once per element
the master would therefore lose one sentinel per element and stop being a master.
So this file cites the two halves that `nondestructive_copy_two_pass` itself cites --
`ShiTM.counted_loop_transfers_prefix_with_marks` for pass 1 and
`ShiTM.copy_loop_transfers_stack` for pass 2 -- and interposes ONE extra `step`, a bare
`push kml fca`, which restores the sentinel on the emptied master exactly when the master
holds only `ta`.  Pass 2 then re-pushes the piece list on top of it, giving
`T kml = pa ++ cma :: ta = S kml` on the nose.  `copy_loop_transfers_stack` is also what
drains the junk out of the working stack (into the discard stack `kd`, which no invariant
mentions), since `Stmt.push` prepends and cannot overwrite.

## The derived cost, and the correction to the plan's estimate

Per working stack: `(S kw).length + 1` to drain the junk, `pa.length + 1` for pass 1,
`1` for the sentinel re-push, `pa.length + 1` for pass 2 -- total
`(S kw).length + 2 * pa.length + 4`.  For the two stacks,
`(S kl).length + (S kb).length + 2 * (pa.length + pb.length) + 8`, and with
`pa.length = (PL ps).length = (ps.map Prod.fst).sum + ps.length` (and the same at `kb`)
that is `2 * (Σa + Σb + 2 * ps.length) + 8` PLUS the two junk lengths.  The plan's
estimate `2 * (Σa + Σb + 2 * ps.length) + 4` counted only the two copy passes: it omits
the two sentinel re-pushes and the two drain-terminating iterations (`+4`), and the junk
itself.  Under WIRE-2's own post-state the junk is bounded by the piece lists, giving the
clean bound `3 * ((PL ps).length + (PB ps).length) + 8`, which is still a CONSTANT of the
fixed piece list, so an element cost function stays a function of the element alone.

## Composability

Rather than naming an invariant, the conclusion carries the higher-order transparency
conjunct `∀ P, (∀ A B, frame → P A → P B) → P S → P T`, so a consumer instantiates `P`
with its own `Inv` and needs no bridging lemma.  The frame is off
`{kl, kb, kml, kmb, ks, kd}` only, so in particular the layout block's index output stack
`ku` and its discard stack `kr` are untouched.
-/

/-! ### One-`stepAux`-node lemmas -/

private theorem shiRl_aux_push {K : Type} [DecidableEq K] {Gam : K → Type} {Lam sig : Type}
    (k : K) (f : sig → Gam k) (Q : Stmt Gam Lam sig) (v : sig) (S : ∀ j, List (Gam j)) :
    stepAux (Stmt.push k f Q) v S
      = stepAux Q v (Function.update S k (f v :: S k)) := rfl

private theorem shiRl_aux_goto {K : Type} [DecidableEq K] {Gam : K → Type} {Lam sig : Type}
    (fl : sig → Lam) (v : sig) (S : ∀ j, List (Gam j)) :
    stepAux (Stmt.goto fl) v S = { l := some (fl v), var := v, stk := S } := rfl

/-- A bare `push`-then-`goto` node costs exactly one `step`. -/
private theorem shiRl_step_push {K : Type} [DecidableEq K] {Gam : K → Type} {Lam sig : Type}
    (M : Lam → Stmt Gam Lam sig) {k : K} {la lb : Lam} {f : sig → Gam k}
    (hM : M la = Stmt.push k f (Stmt.goto (fun _ => lb)))
    (v : sig) (a : Gam k) (hf : f v = a) (S : ∀ q, List (Gam q)) :
    (fun cf : Option (Cfg Gam Lam sig) => cf.bind (step M))^[1]
        (some { l := some la, var := v, stk := S })
      = some { l := some lb, var := v, stk := Function.update S k (a :: S k) } := by
  have h0 : (fun cf : Option (Cfg Gam Lam sig) => cf.bind (step M))^[1]
      (some { l := some la, var := v, stk := S })
      = some (stepAux (M la) v S) := by
    rw [Function.iterate_one]
    all_goals rfl
  rw [h0, hM, shiRl_aux_push, shiRl_aux_goto, hf]
  all_goals rfl

/-! ### List algebra for the mark stack -/

private theorem shiRl_rev_map {A B : Type} (g : A → B) :
    ∀ q : List A, List.map g q.reverse = (List.map g q).reverse := by
  intro q
  induction q with
  | nil => rfl
  | cons a t ih =>
      simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil, ih]

private theorem shiRl_map_inv {A B : Type} (mk : A → B) (e2 : B → A)
    (hinv : ∀ y : A, e2 (mk y) = y) :
    ∀ q : List A, List.map e2 (List.map mk q) = q := by
  intro q
  induction q with
  | nil => rfl
  | cons a t ih => simp only [List.map_cons, hinv, ih]

private theorem shiRl_marks_back {A B : Type} (mk : A → B) (e2 : B → A)
    (hinv : ∀ y : A, e2 (mk y) = y) (p : List A) :
    (List.map e2 (List.map mk p).reverse).reverse = p := by
  rw [shiRl_rev_map e2 (List.map mk p), List.reverse_reverse, shiRl_map_inv mk e2 hinv]

/-! ### The one-stack reload pass -/

private theorem shiRl_one {K : Type} [DecidableEq K] {Gam : K → Type} {Lam sig : Type}
    (M : Lam → Stmt Gam Lam sig) {kw km ks kd : K}
    (hwm : kw ≠ km) (hws : kw ≠ ks) (hwd : kw ≠ kd)
    (hms : km ≠ ks) (hmd : km ≠ kd) (hsd : ks ≠ kd)
    {ldr l1 lx l2 lnd : Lam}
    {fD : sig → Option (Gam kw) → sig} {gD : sig → Bool} {hDp : sig → Gam kd}
    {f1 : sig → Option (Gam km) → sig} {g1 : sig → Bool}
    {h1p : sig → Gam kw} {hmp : sig → Gam ks} {fc : sig → Gam km}
    {f2 : sig → Option (Gam ks) → sig} {g2 : sig → Bool} {h2p : sig → Gam km}
    (eD : Gam kw → Gam kd) (e1 : Gam km → Gam kw) (mk : Gam km → Gam ks)
    (e2 : Gam ks → Gam km)
    (hMdr : M ldr = Stmt.pop kw fD (Stmt.branch gD
              (Stmt.push kd hDp (Stmt.goto (fun _ => ldr)))
              (Stmt.goto (fun _ => l1))))
    (hM1 : M l1 = Stmt.pop km f1 (Stmt.branch g1
              (Stmt.push kw h1p (Stmt.push ks hmp (Stmt.goto (fun _ => l1))))
              (Stmt.goto (fun _ => lx))))
    (hMx : M lx = Stmt.push km fc (Stmt.goto (fun _ => l2)))
    (hM2 : M l2 = Stmt.pop ks f2 (Stmt.branch g2
              (Stmt.push km h2p (Stmt.goto (fun _ => l2)))
              (Stmt.goto (fun _ => lnd))))
    (hDc : ∀ (w : sig) (y : Gam kw), gD (fD w (some y)) = true)
    (hDn : ∀ w : sig, gD (fD w none) = false)
    (hDv : ∀ (w : sig) (y : Gam kw), hDp (fD w (some y)) = eD y)
    (h1v : ∀ (w : sig) (y : Gam km), h1p (f1 w (some y)) = e1 y)
    (hmv : ∀ (w : sig) (y : Gam km), hmp (f1 w (some y)) = mk y)
    (h2c : ∀ (w : sig) (z : Gam ks), g2 (f2 w (some z)) = true)
    (h2n : ∀ w : sig, g2 (f2 w none) = false)
    (h2v : ∀ (w : sig) (z : Gam ks), h2p (f2 w (some z)) = e2 z)
    (hinv : ∀ y : Gam km, e2 (mk y) = y)
    (cm : Gam km) (hfc : ∀ w : sig, fc w = cm)
    (p tm : List (Gam km))
    (h1c : ∀ (w : sig) (y : Gam km), y ∈ p → g1 (f1 w (some y)) = true)
    (hstp : ∀ w : sig, g1 (f1 w (some cm)) = false)
    (L : List (Gam kw)) (hL : (List.map e1 p).reverse = L)
    (v : sig) (S : ∀ k, List (Gam k))
    (hSm : S km = p ++ cm :: tm) (hSs : S ks = []) :
    ∃ (v' : sig) (T : ∀ k, List (Gam k)),
      (fun cf : Option (Cfg Gam Lam sig) => cf.bind (step M))^[(S kw).length
          + 2 * p.length + 4]
          (some { l := some ldr, var := v, stk := S })
        = some { l := some lnd, var := v', stk := T }
      ∧ T kw = L
      ∧ T km = S km
      ∧ T ks = []
      ∧ (∀ k, k ≠ kw → k ≠ km → k ≠ ks → k ≠ kd → T k = S k) := by
  obtain ⟨v1, S1, hr1, p1w, p1m, p1s, p1f⟩ :
      ∃ (v1 : sig) (S1 : ∀ k, List (Gam k)),
        (fun cf : Option (Cfg Gam Lam sig) => cf.bind (step M))^[(S kw).length + 1]
            (some { l := some ldr, var := v, stk := S })
          = some { l := some l1, var := v1, stk := S1 }
        ∧ S1 kw = []
        ∧ S1 km = p ++ cm :: tm
        ∧ S1 ks = []
        ∧ (∀ k, k ≠ kw → k ≠ kd → S1 k = S k) := by
    refine ⟨_, _, (ShiTM.copy_loop_transfers_stack M hwd hMdr hDc hDn hDv (S kw) v S rfl).1,
      ?_, ?_, ?_, ?_⟩
    · rw [Function.update_of_ne hwd, Function.update_self]
      all_goals rfl
    · rw [Function.update_of_ne hmd, Function.update_of_ne (Ne.symm hwm), hSm]
      all_goals rfl
    · rw [Function.update_of_ne hsd, Function.update_of_ne (Ne.symm hws), hSs]
      all_goals rfl
    · intro k ha hb
      rw [Function.update_of_ne hb, Function.update_of_ne ha]
      all_goals rfl
  obtain ⟨v2, S2, hr2, p2w, p2m, p2s, p2f⟩ :
      ∃ (v2 : sig) (S2 : ∀ k, List (Gam k)),
        (fun cf : Option (Cfg Gam Lam sig) => cf.bind (step M))^[p.length + 1]
            (some { l := some l1, var := v1, stk := S1 })
          = some { l := some lx, var := v2, stk := S2 }
        ∧ S2 kw = L
        ∧ S2 km = tm
        ∧ S2 ks = (List.map mk p).reverse
        ∧ (∀ k, k ≠ kw → k ≠ km → k ≠ ks → S2 k = S1 k) := by
    refine ⟨_, _, (ShiTM.counted_loop_transfers_prefix_with_marks M (Ne.symm hwm) hms hws
      hM1 h1v hmv p h1c cm hstp tm v1 S1 p1m).1, ?_, ?_, ?_, ?_⟩
    · rw [Function.update_of_ne hws, Function.update_self, p1w, List.append_nil, hL]
      all_goals rfl
    · rw [Function.update_of_ne hms, Function.update_of_ne (Ne.symm hwm),
        Function.update_self]
      all_goals rfl
    · rw [Function.update_self, p1s, List.append_nil]
      all_goals rfl
    · intro k ha hb hc
      rw [Function.update_of_ne hc, Function.update_of_ne ha, Function.update_of_ne hb]
      all_goals rfl
  obtain ⟨S3, hr3, p3w, p3m, p3s, p3f⟩ :
      ∃ S3 : ∀ k, List (Gam k),
        (fun cf : Option (Cfg Gam Lam sig) => cf.bind (step M))^[1]
            (some { l := some lx, var := v2, stk := S2 })
          = some { l := some l2, var := v2, stk := S3 }
        ∧ S3 kw = L
        ∧ S3 km = cm :: tm
        ∧ S3 ks = (List.map mk p).reverse
        ∧ (∀ k, k ≠ km → S3 k = S2 k) := by
    refine ⟨_, shiRl_step_push M hMx v2 cm (hfc v2) S2, ?_, ?_, ?_, ?_⟩
    · rw [Function.update_of_ne hwm, p2w]
      all_goals rfl
    · rw [Function.update_self, p2m]
      all_goals rfl
    · rw [Function.update_of_ne (Ne.symm hms), p2s]
      all_goals rfl
    · intro k ha
      rw [Function.update_of_ne ha]
      all_goals rfl
  obtain ⟨v4, S4, hr4, p4w, p4m, p4s, p4f⟩ :
      ∃ (v4 : sig) (S4 : ∀ k, List (Gam k)),
        (fun cf : Option (Cfg Gam Lam sig) => cf.bind (step M))^[p.length + 1]
            (some { l := some l2, var := v2, stk := S3 })
          = some { l := some lnd, var := v4, stk := S4 }
        ∧ S4 kw = L
        ∧ S4 km = p ++ cm :: tm
        ∧ S4 ks = []
        ∧ (∀ k, k ≠ km → k ≠ ks → S4 k = S3 k) := by
    have hcp := ShiTM.copy_loop_transfers_stack M (Ne.symm hms) hM2 h2c h2n h2v
      ((List.map mk p).reverse) v2 S3 p3s
    have hlen : ((List.map mk p).reverse).length = p.length := by
      rw [List.length_reverse, List.length_map]
    rw [hlen] at hcp
    refine ⟨_, _, hcp.1, ?_, ?_, ?_, ?_⟩
    · rw [Function.update_of_ne hwm, Function.update_of_ne hws, p3w]
      all_goals rfl
    · rw [Function.update_self, shiRl_marks_back mk e2 hinv p, p3m]
      all_goals rfl
    · rw [Function.update_of_ne (Ne.symm hms), Function.update_self]
      all_goals rfl
    · intro k ha hb
      rw [Function.update_of_ne ha, Function.update_of_ne hb]
      all_goals rfl
  refine ⟨v4, S4, ?_, p4w, ?_, p4s, ?_⟩
  · have he : (S kw).length + 2 * p.length + 4
        = (p.length + 1) + (1 + ((p.length + 1) + ((S kw).length + 1))) := by omega
    rw [he, Function.iterate_add_apply _ (p.length + 1)
        (1 + ((p.length + 1) + ((S kw).length + 1))),
      Function.iterate_add_apply _ 1 ((p.length + 1) + ((S kw).length + 1)),
      Function.iterate_add_apply _ (p.length + 1) ((S kw).length + 1), hr1, hr2, hr3, hr4]
    all_goals rfl
  · rw [p4m, hSm]
    all_goals rfl
  · intro k ha hb hc hd
    rw [p4f k hb hc, p3f k hb, p2f k ha hb hc, p1f k ha hd]
    all_goals rfl

/-! ### The two-stack piece-list reload pass -/

private theorem shiRl_two
    {K : Type} [DecidableEq K] {Gam : K → Type} {Lam sig : Type}
    (M : Lam → Stmt Gam Lam sig) {kl kb kml kmb ks kd : K}
    (h01 : kl ≠ kb) (h02 : kl ≠ kml) (h03 : kl ≠ kmb) (h04 : kl ≠ ks) (h05 : kl ≠ kd)
    (h12 : kb ≠ kml) (h13 : kb ≠ kmb) (h14 : kb ≠ ks) (h15 : kb ≠ kd)
    (h23 : kml ≠ kmb) (h24 : kml ≠ ks) (h25 : kml ≠ kd)
    (h34 : kmb ≠ ks) (h35 : kmb ≠ kd) (h45 : ks ≠ kd)
    {ldr1 la1 lx1 lp1 ldr2 la2 lx2 lp2 lnd : Lam}
    {fDa : sig → Option (Gam kl) → sig} {gDa : sig → Bool} {hDa : sig → Gam kd}
    {f1a : sig → Option (Gam kml) → sig} {g1a : sig → Bool}
    {h1a : sig → Gam kl} {hma : sig → Gam ks} {fca : sig → Gam kml}
    {f2a : sig → Option (Gam ks) → sig} {g2a : sig → Bool} {h2a : sig → Gam kml}
    {fDb : sig → Option (Gam kb) → sig} {gDb : sig → Bool} {hDb : sig → Gam kd}
    {f1b : sig → Option (Gam kmb) → sig} {g1b : sig → Bool}
    {h1b : sig → Gam kb} {hmb : sig → Gam ks} {fcb : sig → Gam kmb}
    {f2b : sig → Option (Gam ks) → sig} {g2b : sig → Bool} {h2b : sig → Gam kmb}
    (eDa : Gam kl → Gam kd) (e1a : Gam kml → Gam kl) (mka : Gam kml → Gam ks)
    (e2a : Gam ks → Gam kml)
    (eDb : Gam kb → Gam kd) (e1b : Gam kmb → Gam kb) (mkb : Gam kmb → Gam ks)
    (e2b : Gam ks → Gam kmb)
    (hMda : M ldr1 = Stmt.pop kl fDa (Stmt.branch gDa
              (Stmt.push kd hDa (Stmt.goto (fun _ => ldr1)))
              (Stmt.goto (fun _ => la1))))
    (hMaa : M la1 = Stmt.pop kml f1a (Stmt.branch g1a
              (Stmt.push kl h1a (Stmt.push ks hma (Stmt.goto (fun _ => la1))))
              (Stmt.goto (fun _ => lx1))))
    (hMxa : M lx1 = Stmt.push kml fca (Stmt.goto (fun _ => lp1)))
    (hMpa : M lp1 = Stmt.pop ks f2a (Stmt.branch g2a
              (Stmt.push kml h2a (Stmt.goto (fun _ => lp1)))
              (Stmt.goto (fun _ => ldr2))))
    (hMdb : M ldr2 = Stmt.pop kb fDb (Stmt.branch gDb
              (Stmt.push kd hDb (Stmt.goto (fun _ => ldr2)))
              (Stmt.goto (fun _ => la2))))
    (hMab : M la2 = Stmt.pop kmb f1b (Stmt.branch g1b
              (Stmt.push kb h1b (Stmt.push ks hmb (Stmt.goto (fun _ => la2))))
              (Stmt.goto (fun _ => lx2))))
    (hMxb : M lx2 = Stmt.push kmb fcb (Stmt.goto (fun _ => lp2)))
    (hMpb : M lp2 = Stmt.pop ks f2b (Stmt.branch g2b
              (Stmt.push kmb h2b (Stmt.goto (fun _ => lp2)))
              (Stmt.goto (fun _ => lnd))))
    (hDca : ∀ (w : sig) (y : Gam kl), gDa (fDa w (some y)) = true)
    (hDna : ∀ w : sig, gDa (fDa w none) = false)
    (hDva : ∀ (w : sig) (y : Gam kl), hDa (fDa w (some y)) = eDa y)
    (h1va : ∀ (w : sig) (y : Gam kml), h1a (f1a w (some y)) = e1a y)
    (hmva : ∀ (w : sig) (y : Gam kml), hma (f1a w (some y)) = mka y)
    (h2ca : ∀ (w : sig) (z : Gam ks), g2a (f2a w (some z)) = true)
    (h2na : ∀ w : sig, g2a (f2a w none) = false)
    (h2va : ∀ (w : sig) (z : Gam ks), h2a (f2a w (some z)) = e2a z)
    (hinva : ∀ y : Gam kml, e2a (mka y) = y)
    (hDcb : ∀ (w : sig) (y : Gam kb), gDb (fDb w (some y)) = true)
    (hDnb : ∀ w : sig, gDb (fDb w none) = false)
    (hDvb : ∀ (w : sig) (y : Gam kb), hDb (fDb w (some y)) = eDb y)
    (h1vb : ∀ (w : sig) (y : Gam kmb), h1b (f1b w (some y)) = e1b y)
    (hmvb : ∀ (w : sig) (y : Gam kmb), hmb (f1b w (some y)) = mkb y)
    (h2cb : ∀ (w : sig) (z : Gam ks), g2b (f2b w (some z)) = true)
    (h2nb : ∀ w : sig, g2b (f2b w none) = false)
    (h2vb : ∀ (w : sig) (z : Gam ks), h2b (f2b w (some z)) = e2b z)
    (hinvb : ∀ y : Gam kmb, e2b (mkb y) = y)
    (cma : Gam kml) (hfca : ∀ w : sig, fca w = cma)
    (cmb : Gam kmb) (hfcb : ∀ w : sig, fcb w = cmb)
    (pa ta : List (Gam kml))
    (h1ca : ∀ (w : sig) (y : Gam kml), y ∈ pa → g1a (f1a w (some y)) = true)
    (hstpa : ∀ w : sig, g1a (f1a w (some cma)) = false)
    (pb tb : List (Gam kmb))
    (h1cb : ∀ (w : sig) (y : Gam kmb), y ∈ pb → g1b (f1b w (some y)) = true)
    (hstpb : ∀ w : sig, g1b (f1b w (some cmb)) = false)
    (PL : List (ℕ × ℕ) → List (Gam kl)) (PB : List (ℕ × ℕ) → List (Gam kb))
    (ps : List (ℕ × ℕ))
    (hpla : (List.map e1a pa).reverse = PL ps)
    (hplb : (List.map e1b pb).reverse = PB ps)
    (v : sig) (S : ∀ k, List (Gam k))
    (hSma : S kml = pa ++ cma :: ta) (hSmb : S kmb = pb ++ cmb :: tb)
    (hSs : S ks = []) :
    ∃ (v' : sig) (T : ∀ k, List (Gam k)),
      (fun cf : Option (Cfg Gam Lam sig) => cf.bind (step M))^[(S kl).length
          + (S kb).length + 2 * (pa.length + pb.length) + 8]
          (some { l := some ldr1, var := v, stk := S })
        = some { l := some lnd, var := v', stk := T }
      ∧ T kl = PL ps
      ∧ T kb = PB ps
      ∧ T kml = S kml
      ∧ T kmb = S kmb
      ∧ T ks = []
      ∧ (∀ k, k ≠ kl → k ≠ kb → k ≠ kml → k ≠ kmb → k ≠ ks → k ≠ kd → T k = S k)
      ∧ (∀ P : (∀ k, List (Gam k)) → Prop,
          (∀ A B : (∀ k, List (Gam k)),
            (∀ k, k ≠ kl → k ≠ kb → k ≠ kml → k ≠ kmb → k ≠ ks → k ≠ kd → A k = B k) →
              P A → P B) →
            P S → P T)
      ∧ Nonempty (StateTransition.EvalsToInTime (step M)
          { l := some ldr1, var := v, stk := S }
          (some { l := some lnd, var := v', stk := T })
          ((S kl).length + (S kb).length + 2 * (pa.length + pb.length) + 8))
      ∧ (PL ps).length = pa.length
      ∧ (PB ps).length = pb.length
      ∧ ((S kl).length ≤ (PL ps).length → (S kb).length ≤ (PB ps).length →
          (S kl).length + (S kb).length + 2 * (pa.length + pb.length) + 8
            ≤ 3 * ((PL ps).length + (PB ps).length) + 8) := by
  obtain ⟨v1, T1, hr1, q1l, q1m, q1s, q1f⟩ := shiRl_one M h02 h04 h05 h24 h25 h45
    eDa e1a mka e2a hMda hMaa hMxa hMpa hDca hDna hDva h1va hmva h2ca h2na h2va hinva
    cma hfca pa ta h1ca hstpa (PL ps) hpla v S hSma hSs
  have ekb : T1 kb = S kb := q1f kb (Ne.symm h01) h12 h14 h15
  have ekmb : T1 kmb = S kmb := q1f kmb (Ne.symm h03) (Ne.symm h23) h34 h35
  obtain ⟨v2, T2, hr2, q2l, q2m, q2s, q2f⟩ := shiRl_one M h13 h14 h15 h34 h35 h45
    eDb e1b mkb e2b hMdb hMab hMxb hMpb hDcb hDnb hDvb h1vb hmvb h2cb h2nb h2vb hinvb
    cmb hfcb pb tb h1cb hstpb (PB ps) hplb v1 T1 (ekmb.trans hSmb) q1s
  rw [ekb] at hr2
  have hTl : T2 kl = PL ps := by
    rw [q2f kl h01 h03 h04 h05, q1l]
    all_goals rfl
  have hTml : T2 kml = S kml := by
    rw [q2f kml (Ne.symm h12) h23 h24 h25, q1m]
    all_goals rfl
  have hTmb : T2 kmb = S kmb := by
    rw [q2m, ekmb]
    all_goals rfl
  have hfr : ∀ k, k ≠ kl → k ≠ kb → k ≠ kml → k ≠ kmb → k ≠ ks → k ≠ kd → T2 k = S k := by
    intro k a b c d e f
    rw [q2f k b d e f, q1f k a c e f]
    all_goals rfl
  have hlA : (PL ps).length = pa.length := by
    rw [← hpla, List.length_reverse, List.length_map]
  have hlB : (PB ps).length = pb.length := by
    rw [← hplb, List.length_reverse, List.length_map]
  have hrun : (fun cf : Option (Cfg Gam Lam sig) => cf.bind (step M))^[(S kl).length
      + (S kb).length + 2 * (pa.length + pb.length) + 8]
      (some { l := some ldr1, var := v, stk := S })
      = some { l := some lnd, var := v2, stk := T2 } := by
    have he : (S kl).length + (S kb).length + 2 * (pa.length + pb.length) + 8
        = ((S kb).length + 2 * pb.length + 4) + ((S kl).length + 2 * pa.length + 4) := by
      omega
    rw [he, Function.iterate_add_apply _ ((S kb).length + 2 * pb.length + 4)
      ((S kl).length + 2 * pa.length + 4), hr1, hr2]
    all_goals rfl
  refine ⟨v2, T2, hrun, hTl, q2l, hTml, hTmb, q2s, hfr, ?_, ?_, hlA, hlB, ?_⟩
  · exact fun P hP hSP => hP S T2 (fun k a b c d e f => (hfr k a b c d e f).symm) hSP
  · exact ⟨⟨(S kl).length + (S kb).length + 2 * (pa.length + pb.length) + 8, hrun⟩,
      le_refl _⟩
  · intro hi hj
    omega

/-! ### A concrete witness machine, run from a NON-TRIVIAL starting state

Six stacks over ONE alphabet `Option Bool`: `none` is the master sentinel, `some true` a
piece mark, `some false` a piece delimiter.  Keys `0 = kl`, `1 = kb`, `2 = kml`,
`3 = kmb`, `4 = ks`, `5 = kd`.  The target lists are the expansions of the two-piece list
`[(2, 1), (1, 3)]`, whose pieces have DIFFERENT lengths:
`PL = [m, m, d, m, d]` (5 symbols) and `PB = [m, d, m, m, m, d]` (6 symbols).
The working stacks start GENUINELY SHORTER than their targets -- `kl` holds two junk
symbols and `kb` one, which is the real post-WIRE-2 situation -- so the pass is not a
no-op anywhere.  Cost: `2 + 1 + 2 * (5 + 6) + 8 = 33`. -/

private abbrev wGm : Fin 6 → Type := fun _ => Option Bool

private abbrev wSig : Type := Option (Option Bool)

private def wpop : wSig → Option (Option Bool) → wSig := fun _ o => o

private def wgall : wSig → Bool := fun s => s.isSome

private def wgcon : wSig → Bool := fun s =>
  match s with
  | some (some _) => true
  | _ => false

private def wval : wSig → Option Bool := fun s => s.getD (some true)

private def wsen : wSig → Option Bool := fun _ => none

private def wM : ℕ → Stmt wGm ℕ wSig
  | 0 => Stmt.pop 0 wpop (Stmt.branch wgall
            (Stmt.push 5 wval (Stmt.goto (fun _ => 0)))
            (Stmt.goto (fun _ => 1)))
  | 1 => Stmt.pop 2 wpop (Stmt.branch wgcon
            (Stmt.push 0 wval (Stmt.push 4 wval (Stmt.goto (fun _ => 1))))
            (Stmt.goto (fun _ => 2)))
  | 2 => Stmt.push 2 wsen (Stmt.goto (fun _ => 3))
  | 3 => Stmt.pop 4 wpop (Stmt.branch wgall
            (Stmt.push 2 wval (Stmt.goto (fun _ => 3)))
            (Stmt.goto (fun _ => 4)))
  | 4 => Stmt.pop 1 wpop (Stmt.branch wgall
            (Stmt.push 5 wval (Stmt.goto (fun _ => 4)))
            (Stmt.goto (fun _ => 5)))
  | 5 => Stmt.pop 3 wpop (Stmt.branch wgcon
            (Stmt.push 1 wval (Stmt.push 4 wval (Stmt.goto (fun _ => 5))))
            (Stmt.goto (fun _ => 6)))
  | 6 => Stmt.push 3 wsen (Stmt.goto (fun _ => 7))
  | 7 => Stmt.pop 4 wpop (Stmt.branch wgall
            (Stmt.push 3 wval (Stmt.goto (fun _ => 7)))
            (Stmt.goto (fun _ => 8)))
  | _ => Stmt.goto (fun _ => 8)

private def wLL : List (Option Bool) :=
  [some true, some true, some false, some true, some false]

private def wBB : List (Option Bool) :=
  [some true, some false, some true, some true, some true, some false]

private def wPA : List (Option Bool) :=
  [some false, some true, some false, some true, some true]

private def wPC : List (Option Bool) :=
  [some false, some true, some true, some true, some false, some true]

private def wS : ∀ k : Fin 6, List (wGm k)
  | 0 => [some true, some false]
  | 1 => [some false]
  | 2 => wPA ++ [none]
  | 3 => wPC ++ [none]
  | 4 => []
  | 5 => []

private theorem wPAc : ∀ (w : wSig) (y : Option Bool), y ∈ wPA →
    wgcon (wpop w (some y)) = true := by
  intro w y hy
  cases y with
  | none => simp [wPA] at hy
  | some b => rfl

private theorem wPCc : ∀ (w : wSig) (y : Option Bool), y ∈ wPC →
    wgcon (wpop w (some y)) = true := by
  intro w y hy
  cases y with
  | none => simp [wPC] at hy
  | some b => rfl
private theorem shiRl_witness :
    ∃ (Gm : Fin 6 → Type) (Lm sg : Type) (Mw : Lm → Stmt Gm Lm sg)
      (kl kb kml kmb ks kd : Fin 6) (lst lfn : Lm)
      (Sw Tw : ∀ k, List (Gm k)) (u0 u1 : sg)
      (LL : List (Gm kl)) (BB : List (Gm kb)),
      ([kl, kb, kml, kmb, ks, kd] : List (Fin 6)).Nodup
      ∧ lst ≠ lfn
      ∧ LL.length = 5
      ∧ BB.length = 6
      ∧ (Sw kl).length = 2
      ∧ (Sw kb).length = 1
      ∧ (Sw kl).length < LL.length
      ∧ (Sw kb).length < BB.length
      ∧ Sw kl ≠ LL
      ∧ Sw kb ≠ BB
      ∧ Sw ks = []
      ∧ Sw kml ≠ []
      ∧ Sw kmb ≠ []
      ∧ (fun cf : Option (Cfg Gm Lm sg) => cf.bind (step Mw))^[33]
          (some { l := some lst, var := u0, stk := Sw })
        = some { l := some lfn, var := u1, stk := Tw }
      ∧ Tw kl = LL
      ∧ Tw kb = BB
      ∧ Tw kml = Sw kml
      ∧ Tw kmb = Sw kmb
      ∧ Tw ks = []
      ∧ Nonempty (StateTransition.EvalsToInTime (step Mw)
          { l := some lst, var := u0, stk := Sw }
          (some { l := some lfn, var := u1, stk := Tw }) 33) := by
  obtain ⟨vf, Tf, hrun, hTl, hTb, hTml, hTmb, hTs, hfr, htr, hev, hl1, hl2, hbd⟩ :=
    shiRl_two wM (kl := 0) (kb := 1) (kml := 2) (kmb := 3) (ks := 4) (kd := 5)
      (ldr1 := 0) (la1 := 1) (lx1 := 2) (lp1 := 3) (ldr2 := 4) (la2 := 5) (lx2 := 6)
      (lp2 := 7) (lnd := 8)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (fun y => y) (fun y => y) (fun y => y) (fun y => y)
      (fun y => y) (fun y => y) (fun y => y) (fun y => y)
      rfl rfl rfl rfl rfl rfl rfl rfl
      (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
      (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
      (none : Option Bool) (fun _ => rfl)
      (none : Option Bool) (fun _ => rfl)
      wPA ([] : List (Option Bool)) wPAc (fun _ => rfl)
      wPC ([] : List (Option Bool)) wPCc (fun _ => rfl)
      (fun _ => wLL) (fun _ => wBB) ([(2, 1), (1, 3)] : List (ℕ × ℕ))
      (by rfl) (by rfl)
      (none : wSig) wS (by rfl) (by rfl) (by rfl)
  have h33 : (33 : ℕ) = (wS 0).length + (wS 1).length
      + 2 * (wPA.length + wPC.length) + 8 := by rfl
  have hrun33 : (fun cf : Option (Cfg wGm ℕ wSig) => cf.bind (step wM))^[33]
      (some { l := some 0, var := (none : wSig), stk := wS })
      = some { l := some 8, var := vf, stk := Tf } := by
    rw [h33]
    exact hrun
  exact ⟨wGm, ℕ, wSig, wM, 0, 1, 2, 3, 4, 5, 0, 8, wS, Tf, (none : wSig), vf, wLL, wBB,
    by decide, by decide, rfl, rfl, rfl, rfl, by decide, by decide, by decide, by decide,
    rfl, by decide, by decide, hrun33, hTl, hTb, hTml, hTmb, hTs,
    ⟨⟨33, hrun33⟩, le_refl _⟩⟩

/-! ### The public statement -/

theorem solution :
    (∀
    {K : Type} [DecidableEq K] {Gam : K → Type} {Lam sig : Type}
    (M : Lam → Stmt Gam Lam sig) {kl kb kml kmb ks kd : K}
    (h01 : kl ≠ kb) (h02 : kl ≠ kml) (h03 : kl ≠ kmb) (h04 : kl ≠ ks) (h05 : kl ≠ kd)
    (h12 : kb ≠ kml) (h13 : kb ≠ kmb) (h14 : kb ≠ ks) (h15 : kb ≠ kd)
    (h23 : kml ≠ kmb) (h24 : kml ≠ ks) (h25 : kml ≠ kd)
    (h34 : kmb ≠ ks) (h35 : kmb ≠ kd) (h45 : ks ≠ kd)
    {ldr1 la1 lx1 lp1 ldr2 la2 lx2 lp2 lnd : Lam}
    {fDa : sig → Option (Gam kl) → sig} {gDa : sig → Bool} {hDa : sig → Gam kd}
    {f1a : sig → Option (Gam kml) → sig} {g1a : sig → Bool}
    {h1a : sig → Gam kl} {hma : sig → Gam ks} {fca : sig → Gam kml}
    {f2a : sig → Option (Gam ks) → sig} {g2a : sig → Bool} {h2a : sig → Gam kml}
    {fDb : sig → Option (Gam kb) → sig} {gDb : sig → Bool} {hDb : sig → Gam kd}
    {f1b : sig → Option (Gam kmb) → sig} {g1b : sig → Bool}
    {h1b : sig → Gam kb} {hmb : sig → Gam ks} {fcb : sig → Gam kmb}
    {f2b : sig → Option (Gam ks) → sig} {g2b : sig → Bool} {h2b : sig → Gam kmb}
    (eDa : Gam kl → Gam kd) (e1a : Gam kml → Gam kl) (mka : Gam kml → Gam ks)
    (e2a : Gam ks → Gam kml)
    (eDb : Gam kb → Gam kd) (e1b : Gam kmb → Gam kb) (mkb : Gam kmb → Gam ks)
    (e2b : Gam ks → Gam kmb)
    (hMda : M ldr1 = Stmt.pop kl fDa (Stmt.branch gDa
              (Stmt.push kd hDa (Stmt.goto (fun _ => ldr1)))
              (Stmt.goto (fun _ => la1))))
    (hMaa : M la1 = Stmt.pop kml f1a (Stmt.branch g1a
              (Stmt.push kl h1a (Stmt.push ks hma (Stmt.goto (fun _ => la1))))
              (Stmt.goto (fun _ => lx1))))
    (hMxa : M lx1 = Stmt.push kml fca (Stmt.goto (fun _ => lp1)))
    (hMpa : M lp1 = Stmt.pop ks f2a (Stmt.branch g2a
              (Stmt.push kml h2a (Stmt.goto (fun _ => lp1)))
              (Stmt.goto (fun _ => ldr2))))
    (hMdb : M ldr2 = Stmt.pop kb fDb (Stmt.branch gDb
              (Stmt.push kd hDb (Stmt.goto (fun _ => ldr2)))
              (Stmt.goto (fun _ => la2))))
    (hMab : M la2 = Stmt.pop kmb f1b (Stmt.branch g1b
              (Stmt.push kb h1b (Stmt.push ks hmb (Stmt.goto (fun _ => la2))))
              (Stmt.goto (fun _ => lx2))))
    (hMxb : M lx2 = Stmt.push kmb fcb (Stmt.goto (fun _ => lp2)))
    (hMpb : M lp2 = Stmt.pop ks f2b (Stmt.branch g2b
              (Stmt.push kmb h2b (Stmt.goto (fun _ => lp2)))
              (Stmt.goto (fun _ => lnd))))
    (hDca : ∀ (w : sig) (y : Gam kl), gDa (fDa w (some y)) = true)
    (hDna : ∀ w : sig, gDa (fDa w none) = false)
    (hDva : ∀ (w : sig) (y : Gam kl), hDa (fDa w (some y)) = eDa y)
    (h1va : ∀ (w : sig) (y : Gam kml), h1a (f1a w (some y)) = e1a y)
    (hmva : ∀ (w : sig) (y : Gam kml), hma (f1a w (some y)) = mka y)
    (h2ca : ∀ (w : sig) (z : Gam ks), g2a (f2a w (some z)) = true)
    (h2na : ∀ w : sig, g2a (f2a w none) = false)
    (h2va : ∀ (w : sig) (z : Gam ks), h2a (f2a w (some z)) = e2a z)
    (hinva : ∀ y : Gam kml, e2a (mka y) = y)
    (hDcb : ∀ (w : sig) (y : Gam kb), gDb (fDb w (some y)) = true)
    (hDnb : ∀ w : sig, gDb (fDb w none) = false)
    (hDvb : ∀ (w : sig) (y : Gam kb), hDb (fDb w (some y)) = eDb y)
    (h1vb : ∀ (w : sig) (y : Gam kmb), h1b (f1b w (some y)) = e1b y)
    (hmvb : ∀ (w : sig) (y : Gam kmb), hmb (f1b w (some y)) = mkb y)
    (h2cb : ∀ (w : sig) (z : Gam ks), g2b (f2b w (some z)) = true)
    (h2nb : ∀ w : sig, g2b (f2b w none) = false)
    (h2vb : ∀ (w : sig) (z : Gam ks), h2b (f2b w (some z)) = e2b z)
    (hinvb : ∀ y : Gam kmb, e2b (mkb y) = y)
    (cma : Gam kml) (hfca : ∀ w : sig, fca w = cma)
    (cmb : Gam kmb) (hfcb : ∀ w : sig, fcb w = cmb)
    (pa ta : List (Gam kml))
    (h1ca : ∀ (w : sig) (y : Gam kml), y ∈ pa → g1a (f1a w (some y)) = true)
    (hstpa : ∀ w : sig, g1a (f1a w (some cma)) = false)
    (pb tb : List (Gam kmb))
    (h1cb : ∀ (w : sig) (y : Gam kmb), y ∈ pb → g1b (f1b w (some y)) = true)
    (hstpb : ∀ w : sig, g1b (f1b w (some cmb)) = false)
    (PL : List (ℕ × ℕ) → List (Gam kl)) (PB : List (ℕ × ℕ) → List (Gam kb))
    (ps : List (ℕ × ℕ))
    (hpla : (List.map e1a pa).reverse = PL ps)
    (hplb : (List.map e1b pb).reverse = PB ps)
    (v : sig) (S : ∀ k, List (Gam k))
    (hSma : S kml = pa ++ cma :: ta) (hSmb : S kmb = pb ++ cmb :: tb)
    (hSs : S ks = []),
    ∃ (v' : sig) (T : ∀ k, List (Gam k)),
      (fun cf : Option (Cfg Gam Lam sig) => cf.bind (step M))^[(S kl).length
          + (S kb).length + 2 * (pa.length + pb.length) + 8]
          (some { l := some ldr1, var := v, stk := S })
        = some { l := some lnd, var := v', stk := T }
      ∧ T kl = PL ps
      ∧ T kb = PB ps
      ∧ T kml = S kml
      ∧ T kmb = S kmb
      ∧ T ks = []
      ∧ (∀ k, k ≠ kl → k ≠ kb → k ≠ kml → k ≠ kmb → k ≠ ks → k ≠ kd → T k = S k)
      ∧ (∀ P : (∀ k, List (Gam k)) → Prop,
          (∀ A B : (∀ k, List (Gam k)),
            (∀ k, k ≠ kl → k ≠ kb → k ≠ kml → k ≠ kmb → k ≠ ks → k ≠ kd → A k = B k) →
              P A → P B) →
            P S → P T)
      ∧ Nonempty (StateTransition.EvalsToInTime (step M)
          { l := some ldr1, var := v, stk := S }
          (some { l := some lnd, var := v', stk := T })
          ((S kl).length + (S kb).length + 2 * (pa.length + pb.length) + 8))
      ∧ (PL ps).length = pa.length
      ∧ (PB ps).length = pb.length
      ∧ ((S kl).length ≤ (PL ps).length → (S kb).length ≤ (PB ps).length →
          (S kl).length + (S kb).length + 2 * (pa.length + pb.length) + 8
            ≤ 3 * ((PL ps).length + (PB ps).length) + 8)
    )
    ∧
    ∃ (Gm : Fin 6 → Type) (Lm sg : Type) (Mw : Lm → Stmt Gm Lm sg)
      (kl kb kml kmb ks kd : Fin 6) (lst lfn : Lm)
      (Sw Tw : ∀ k, List (Gm k)) (u0 u1 : sg)
      (LL : List (Gm kl)) (BB : List (Gm kb)),
      ([kl, kb, kml, kmb, ks, kd] : List (Fin 6)).Nodup
      ∧ lst ≠ lfn
      ∧ LL.length = 5
      ∧ BB.length = 6
      ∧ (Sw kl).length = 2
      ∧ (Sw kb).length = 1
      ∧ (Sw kl).length < LL.length
      ∧ (Sw kb).length < BB.length
      ∧ Sw kl ≠ LL
      ∧ Sw kb ≠ BB
      ∧ Sw ks = []
      ∧ Sw kml ≠ []
      ∧ Sw kmb ≠ []
      ∧ (fun cf : Option (Cfg Gm Lm sg) => cf.bind (step Mw))^[33]
          (some { l := some lst, var := u0, stk := Sw })
        = some { l := some lfn, var := u1, stk := Tw }
      ∧ Tw kl = LL
      ∧ Tw kb = BB
      ∧ Tw kml = Sw kml
      ∧ Tw kmb = Sw kmb
      ∧ Tw ks = []
      ∧ Nonempty (StateTransition.EvalsToInTime (step Mw)
          { l := some lst, var := u0, stk := Sw }
          (some { l := some lfn, var := u1, stk := Tw }) 33) := by
  refine ⟨?_, shiRl_witness⟩
  exact shiRl_two
