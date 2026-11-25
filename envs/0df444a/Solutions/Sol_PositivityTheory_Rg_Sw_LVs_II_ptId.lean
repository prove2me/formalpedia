-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.II.ptId
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:25:04.181344+00:00
-- url     : https://prove2.me/submissions/14b3ea4f-71ae-4d98-9047-a361d0700460

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_InfInvA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_FderivXZxSkew
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_II_contDiff_xZx
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_II_cDiff
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_II_reK_add_imK
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_II_dK_xZx
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_II_decomp
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_II_sumA
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_II_sumB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.II
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs.II
theorem _root_.solution : PtId := by
  intro n Θ x Z hx hΘ hlaw
  set M := x * Z * xᴴ with hM
  have hxZ : x * Z = M * x := by rw [hM, Matrix.mul_assoc (x * Z), hx.2, Matrix.mul_one]
  have hΘd : DifferentiableAt ℂ Θ x := hΘ.differentiableAt (by simp)
  have hR : ∀ v, fderiv ℝ Θ x v = fderiv ℂ Θ x v := fun v => by
    have h := (hΘd.hasFDerivAt.restrictScalars ℝ).fderiv
    exact (congrArg (fun L => L v) h).trans rfl
  have hdK : ∀ e, dK Θ x e = fderiv ℂ Θ x (e * x) := fun e => by
    rw [dK, hR, hR]
    conv_rhs => rw [← reK_add_imK e]
    rw [Matrix.add_mul, Matrix.smul_mul, map_add, map_smul, smul_eq_mul]
  have hLeib : ∀ c : M2 n → ℂ, DifferentiableAt ℝ c x → ∀ e,
      dK (fun y => c y * Θ y) x e = dK c x e * Θ x + c x * dK Θ x e := fun c hc e => by
    have hΘr : DifferentiableAt ℝ Θ x := hΘd.restrictScalars ℝ
    have h := (hc.hasFDerivAt.mul hΘr.hasFDerivAt).fderiv
    have hv : ∀ v, fderiv ℝ (fun y => c y * Θ y) x v = c x * fderiv ℝ Θ x v + Θ x * fderiv ℝ c x v := fun v => by
      exact (congrArg (fun L : M2 n →L[ℝ] ℂ => L v) h).trans rfl
    simp only [dK, hv]
    ring
  have hcA : ∀ a b, DifferentiableAt ℝ (cA Z a b) x := fun a b =>
    ((cDiff n Z a b).1.differentiable (by simp)).differentiableAt
  have hcB : ∀ a b, DifferentiableAt ℝ (cB Z a b) x := fun a b =>
    ((cDiff n Z a b).2.differentiable (by simp)).differentiableAt
  have hdA : ∀ a b e, dK (cA Z a b) x e = (e * M - M * e) (Sum.inr a) (Sum.inr b) := fun a b e =>
    dK_xZx Z x e (Sum.inr a) (Sum.inr b)
  have hdB : ∀ a b e, dK (cB Z a b) x e = -((e * M - M * e) (Sum.inr a) (Sum.inl b)) := fun a b e => by
    have : cB Z a b = fun y => -((y * Z * yᴴ) (Sum.inr a) (Sum.inl b)) := rfl
    have hd : DifferentiableAt ℝ (fun y : M2 n => (y * Z * yᴴ) (Sum.inr a) (Sum.inl b)) x :=
      ((contDiff_xZx Z _ _).differentiable (by simp)).differentiableAt
    have hn := hd.hasFDerivAt.neg.fderiv
    have hv : ∀ v, fderiv ℝ (fun y : M2 n => -(y * Z * yᴴ) (Sum.inr a) (Sum.inl b)) x v =
        -fderiv ℝ (fun y : M2 n => (y * Z * yᴴ) (Sum.inr a) (Sum.inl b)) x v := fun v => by
      exact (congrArg (fun L : M2 n →L[ℝ] ℂ => L v) hn).trans rfl
    have h := dK_xZx Z x e (Sum.inr a) (Sum.inl b)
    rw [dK] at h
    rw [this, dK, hv, hv, ← h]; ring

  have hL : fderiv ℂ Θ x (x * Z) = (n : ℂ) * (M.toBlocks₁₁.trace - M.toBlocks₂₂.trace) * Θ x +
      ∑ a, ∑ b, (cA Z a b x * dK Θ x (eA a b) + cB Z a b x * dK Θ x (eB a b)) := by
    rw [hxZ]
    conv_lhs => rw [decomp M]
    rw [Matrix.add_mul, map_add, hlaw _ (by simp)]
    simp only [Matrix.sum_mul, map_sum, Matrix.add_mul, Matrix.smul_mul, map_add, map_smul, smul_eq_mul, hdK]
    congr 1
    · simp [Matrix.trace_sub]
  rw [hL]
  simp only [hLeib _ (hcA _ _), hLeib _ (hcB _ _), hdA, hdB]
  have e1 : ∀ a b, (eA a b * M - M * eA a b) (Sum.inr a) (Sum.inr b) * Θ x + cA Z a b x * dK Θ x (eA a b) +
      (-((eB a b * M - M * eB a b) (Sum.inr a) (Sum.inl b)) * Θ x + cB Z a b x * dK Θ x (eB a b)) =
      ((eA a b * M - M * eA a b) (Sum.inr a) (Sum.inr b) + -((eB a b * M - M * eB a b) (Sum.inr a) (Sum.inl b))) * Θ x +
      (cA Z a b x * dK Θ x (eA a b) + cB Z a b x * dK Θ x (eB a b)) := fun a b => by ring
  simp only [e1, Finset.sum_add_distrib, ← Finset.sum_mul, sumA, sumB]
  ring
end PositivityTheory.Rg.Sw.LVs.II
