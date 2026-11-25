-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AreaGraphBound_proof_3141fa364ca4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:47:54.075953+00:00
-- url     : https://prove2.me/submissions/841c39b7-6c10-442e-bb2e-8a4b29e52807

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAreaGraphBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAreaGraphPiece
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAreaGraphPartition
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGraphJacContinuous
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAreaGraphBound
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_realGraphPt_injective_e476b3e7ecac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_realGraphPt_continuousOn_acf3943910ee

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory
open scoped ENNReal NNReal
namespace GroundTheory.Heights₂.Heights
namespace AreaGraphBound
theorem _root_.solution (h₁ : AreaGraphPiece.Statement) (h₂ : AreaGraphPartition.Statement)
    (h₃ : GraphJacContinuous.Statement) : AreaGraphBound.Statement := by
  intro k m U F hU hF A hAU hA δ hδ0 hδ1
  set J : (EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m)) → ℝ≥0∞ := fun B =>
    ENNReal.ofReal (graphJac (B : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))) with hJ
  set c : ℝ≥0∞ := ((1 + δ : ℝ≥0) : ℝ≥0∞) with hc

  choose r₃ hr₃0 hr₃ using fun B => h₃ k m B δ (by exact_mod_cast hδ0)
  obtain ⟨t, An, hdisj, htm, -, hcov, happrox, hder⟩ :=
    h₂ k m U F hU hF (fun B => min δ (r₃ B).toNNReal)
      (fun B => (lt_min hδ0 (Real.toNNReal_pos.2 (hr₃0 B))).ne')
  set p : ℕ → Set (EuclideanSpace ℝ (Fin k)) := fun n => A ∩ t n with hp
  have hpm : ∀ n, MeasurableSet (p n) := fun n => hA.inter (htm n)
  have hpd : Pairwise (Function.onFun Disjoint p) := fun i j hij =>
    (hdisj hij).mono Set.inter_subset_right Set.inter_subset_right
  have hAp : A = ⋃ n, p n := by
    rw [← Set.inter_iUnion]
    exact (Set.inter_eq_left.2 (hAU.trans hcov)).symm

  have hcmp : ∀ n, ∀ x ∈ p n, J (fderiv ℝ F x) ≤ c * J (An n) ∧ J (An n) ≤ c * J (fderiv ℝ F x) := by
    intro n x hx
    have hle : ‖fderiv ℝ F x - An n‖ ≤ r₃ (An n) := by
      have := (hder n x hx.2).trans (min_le_right _ _)
      have h' : ((‖fderiv ℝ F x - An n‖₊ : ℝ≥0) : ℝ) ≤ ((r₃ (An n)).toNNReal : ℝ) := by exact_mod_cast this
      simpa [Real.coe_toNNReal _ (hr₃0 (An n)).le] using h'
    obtain ⟨h1, h2⟩ := hr₃ (An n) (fderiv ℝ F x) hle
    have e : ∀ y : ℝ, ENNReal.ofReal ((1 + δ) * y) = c * ENNReal.ofReal y := fun y => by
      rw [ENNReal.ofReal_mul (by positivity), hc]; congr 1
      rw [← ENNReal.ofReal_coe_nnreal]; push_cast; rfl
    exact ⟨(ENNReal.ofReal_le_ofReal h1).trans (e _).le, (ENNReal.ofReal_le_ofReal h2).trans (e _).le⟩

  have hpiece : ∀ n, μH[(k : ℝ)] (realGraphPt F '' p n) ≤ c ^ (k + 1) * ∫⁻ x in p n, J (fderiv ℝ F x)
      ∂(μH[(k : ℝ)]) ∧ ((1 - δ : ℝ≥0) : ℝ≥0∞) ^ k * ∫⁻ x in p n, J (fderiv ℝ F x) ∂(μH[(k : ℝ)]) ≤
        c * μH[(k : ℝ)] (realGraphPt F '' p n) := by
    intro n
    obtain ⟨u, l⟩ := h₁ k m F (An n) δ (p n) hδ1
      (((happrox n).mono_set Set.inter_subset_right).mono_num (min_le_left _ _))
    have i₁ : J (An n) * μH[(k : ℝ)] (p n) ≤ c * ∫⁻ x in p n, J (fderiv ℝ F x) ∂(μH[(k : ℝ)]) := by
      rw [← setLIntegral_const, ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
      exact setLIntegral_mono' (hpm n) fun x hx => (hcmp n x hx).2
    have i₂ : ∫⁻ x in p n, J (fderiv ℝ F x) ∂(μH[(k : ℝ)]) ≤ c * (J (An n) * μH[(k : ℝ)] (p n)) := by
      rw [← setLIntegral_const, ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
      exact setLIntegral_mono' (hpm n) fun x hx => (hcmp n x hx).1
    constructor
    · calc _ ≤ c ^ k * (J (An n) * μH[(k : ℝ)] (p n)) := by rw [← mul_assoc]; exact u
        _ ≤ c ^ k * (c * ∫⁻ x in p n, J (fderiv ℝ F x) ∂(μH[(k : ℝ)])) := by gcongr
        _ = _ := by rw [pow_succ, mul_assoc]
    · calc _ ≤ ((1 - δ : ℝ≥0) : ℝ≥0∞) ^ k * (c * (J (An n) * μH[(k : ℝ)] (p n))) := by gcongr
        _ = c * (((1 - δ : ℝ≥0) : ℝ≥0∞) ^ k * J (An n) * μH[(k : ℝ)] (p n)) := by ring
        _ ≤ _ := by gcongr

  have hG : ∀ n, MeasurableSet (realGraphPt F '' p n) := fun n =>
    (hpm n).image_of_continuousOn_injOn
      (realGraphPt_continuousOn (hF.continuousOn.mono (Set.inter_subset_left.trans hAU)))
      (realGraphPt_injective F).injOn
  have hGd : Pairwise (Function.onFun Disjoint fun n => realGraphPt F '' p n) := fun i j hij =>
    (Set.disjoint_image_iff (realGraphPt_injective F)).2 (hpd hij)
  have hS : μH[(k : ℝ)] (realGraphPt F '' A) = ∑' n, μH[(k : ℝ)] (realGraphPt F '' p n) := by
    rw [hAp, Set.image_iUnion, measure_iUnion hGd hG]
  have hI : ∫⁻ x in A, J (fderiv ℝ F x) ∂(μH[(k : ℝ)]) =
      ∑' n, ∫⁻ x in p n, J (fderiv ℝ F x) ∂(μH[(k : ℝ)]) := by
    rw [hAp, lintegral_iUnion hpm hpd]
  change μH[(k : ℝ)] (realGraphPt F '' A) ≤ c ^ (k + 1) * ∫⁻ x in A, J (fderiv ℝ F x) ∂(μH[(k : ℝ)]) ∧
    ((1 - δ : ℝ≥0) : ℝ≥0∞) ^ k * ∫⁻ x in A, J (fderiv ℝ F x) ∂(μH[(k : ℝ)]) ≤
      c * μH[(k : ℝ)] (realGraphPt F '' A)
  rw [hS, hI, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
  exact ⟨ENNReal.tsum_le_tsum fun n => (hpiece n).1, ENNReal.tsum_le_tsum fun n => (hpiece n).2⟩
end AreaGraphBound
end GroundTheory.Heights₂.Heights
