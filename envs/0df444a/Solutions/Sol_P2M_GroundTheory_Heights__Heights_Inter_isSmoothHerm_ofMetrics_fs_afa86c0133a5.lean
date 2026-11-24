-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_isSmoothHerm_ofMetrics_fs_afa86c0133a5
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:04:16.881469+00:00
-- url     : https://prove2.me/submissions/874c064c-fb86-45cf-a978-e858c81fc34b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_TsgPolyVolPolyCoeffEven
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_KappaSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_ContractMixedFieldStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsAntisym
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ofMetrics_fs_h_bd4ac42ff7dd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial Matrix ComplexOrder ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
noncomputable section
attribute [instance] ProjectiveLineBundle.fieldΩ ProjectiveLineBundle.finι ProjectiveLineBundle.finν ProjectiveLineBundle.finκ ProjectiveLineBundle.acgE ProjectiveLineBundle.modE
  ProjectiveLineBundle.fieldΦ ProjectiveLineBundle.algΦ
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution (a : K → ℤ) : IsSmoothHerm (HermLine.ofMetrics (fun k => fsMetric (ι k)) a) := by
  have hfun : (HermLine.ofMetrics (fun k => fsMetric (ι k)) a).h =
      fun z => ∏ k, Real.sqrt (∑ i, ‖z ⟨k, i⟩‖ ^ 2) ^ a k := funext (ofMetrics_fs_h a)
  unfold IsSmoothHerm
  rw [hfun]
  refine contDiffOn_prod fun k _ => ?_
  have hpos : ∀ z ∈ {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}, 0 < ∑ i, ‖z ⟨k, i⟩‖ ^ 2 := by
    intro z hz
    obtain ⟨i, hi⟩ := hz k
    exact Finset.sum_pos' (fun j _ => sq_nonneg ‖z ⟨k, j⟩‖) ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hi) 2⟩
  have hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k, ι k) → ℂ => Real.sqrt (∑ i, ‖z ⟨k, i⟩‖ ^ 2))
      {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} :=
    ContDiffOn.sqrt (ContDiff.sum fun i _ => (contDiff_norm_sq ℝ).comp
      (contDiff_apply ℝ ℂ (⟨k, i⟩ : Σ k, ι k))).contDiffOn fun z hz => (hpos z hz).ne'
  have hf0 : ∀ z ∈ {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}, Real.sqrt (∑ i, ‖z ⟨k, i⟩‖ ^ 2) ≠ 0 :=
    fun z hz => (Real.sqrt_pos.2 (hpos z hz)).ne'
  obtain ⟨m, hm | hm⟩ := Int.eq_nat_or_neg (a k)
  · simp only [hm, zpow_natCast]
    exact hf.pow m
  · simp only [hm, _root_.zpow_neg, zpow_natCast]
    exact (hf.pow m).inv fun z hz => pow_ne_zero _ (hf0 z hz)
end GroundTheory.Heights₂.Heights.Inter
