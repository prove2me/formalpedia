-- Prove2me | solution 1 for StrongConv.not_tendsto_prob_norm_eval_stableRep_ge_sub_printed
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-04T23:19:08.690183+00:00
-- url     : https://prove2.me/submissions/b0a82906-b0d0-4388-b966-b732ea7b14c6

import Mathlib
import Definitions.Def_StrongConv

open Filter Topology Polynomial

namespace StrongConv

noncomputable def zeroRep : StableRep where
  N₀ := 0
  r := 0
  φ := 0
  dim := fun _ => 0
  π := fun _ => 1
  trace_eq := by intro N _ σ; simp [Matrix.trace]

lemma zeroRep_noTrivial : zeroRep.NoTrivialSummand := by
  intro N _ v _; funext i; exact Fin.elim0 i

noncomputable def onePoly : NCPoly 1 0 := Finsupp.single 1 1

lemma eval_onePoly_apply (x : PiLp 2 (fun _ : Fin 1 => L2Free 0)) :
    onePoly.eval (sLimit 0) x = x := by
  classical
  simp only [NCPoly.eval, onePoly]
  rw [Finsupp.support_single _ one_ne_zero, Finset.sum_singleton, Finsupp.single_eq_same]
  simp only [wordOp, FreeMonoid.toList_one, List.map_nil, List.prod_nil, tensorOp]
  ext i
  fin_cases i
  simp

lemma norm_eval_model_zero {N : ℕ} (σ : Fin 0 → Equiv.Perm (Fin N)) :
    ‖onePoly.eval (zeroRep.model σ)‖ = 0 := by
  have : Subsingleton (PiLp 2 (fun _ : Fin 1 => EuclideanSpace ℂ (Fin (zeroRep.dim N)))) := by
    constructor; intro a b; ext i j; exact Fin.elim0 j
  rw [norm_eq_zero]; ext x; simp [Subsingleton.elim x 0]

lemma one_le_norm_eval_onePoly : 1 ≤ ‖onePoly.eval (sLimit 0)‖ := by
  set x : PiLp 2 (fun _ : Fin 1 => L2Free 0) := PiLp.single 2 0 (delta 1) with hx
  have hxn : ‖x‖ = 1 := by
    simp [hx, delta]
  have := (onePoly.eval (sLimit 0)).le_opNorm x
  rw [eval_onePoly_apply, hxn] at this
  simpa using this

theorem not_tendsto_dev :
    ¬ ∀ (π : StableRep), π.NoTrivialSummand → ∀ {D d : ℕ} (P : NCPoly D d) (δ : ℝ), 0 < δ →
      Tendsto (fun N : ℕ => uniformProb (fun σ : Fin d → Equiv.Perm (Fin N) =>
        ‖P.eval (sLimit d)‖ - δ ≤ ‖P.eval (π.model σ)‖)) atTop (𝓝 1) := by
  intro h
  have ht := h zeroRep zeroRep_noTrivial onePoly (1 / 2) (by norm_num)
  have h0 : (fun N : ℕ => uniformProb (fun σ : Fin 0 → Equiv.Perm (Fin N) =>
      ‖onePoly.eval (sLimit 0)‖ - 1 / 2 ≤ ‖onePoly.eval (zeroRep.model σ)‖)) = fun _ => 0 := by
    funext N
    have hlt : ∀ σ : Fin 0 → Equiv.Perm (Fin N),
        ¬ (‖onePoly.eval (sLimit 0)‖ - 1 / 2 ≤ ‖onePoly.eval (zeroRep.model σ)‖) := by
      intro σ
      rw [norm_eval_model_zero]
      have := one_le_norm_eval_onePoly
      linarith
    classical
    unfold uniformProb
    rw [Finset.filter_false_of_mem (fun σ _ => hlt σ)]
    simp
  rw [h0] at ht
  have := tendsto_nhds_unique ht tendsto_const_nhds
  norm_num at this

end StrongConv

theorem solution : type_of% @StrongConv.not_tendsto_dev := @StrongConv.not_tendsto_dev
