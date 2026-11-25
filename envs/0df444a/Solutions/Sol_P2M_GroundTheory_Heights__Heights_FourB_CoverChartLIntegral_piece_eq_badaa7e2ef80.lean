-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FourB_CoverChartLIntegral_piece_eq_badaa7e2ef80
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:28:05.665339+00:00
-- url     : https://prove2.me/submissions/fa45ff41-6b7a-40db-898b-75c9a2c5c573

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_StatementsCoverInt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Degree
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PLCurveA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PCoverChartLIntegral
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_CoverChartLIntegral_analyticAt_chart_d65b277122cd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_CoverChartLIntegral_measurableSet_piece_35bf42420ffc
import Theorems.Thm_ReciprocityTheory_AnForm_M_degree_det_restrictScalars
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open ReciprocityTheory.AnForm.M MeasureTheory Topology
noncomputable section
open GroundTheory.Heights₂.Heights.FourB.CoverChartLIntegral
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace GroundTheory.Heights₂.Heights.FourB.CoverChartLIntegral
theorem _root_.solution {A : FinHolAtlas e X} (χ : ChartPartition A) (j : Fin A.n) {q : X → Fin e → ℂ}
    {M₀ : Set X} (hholo : ∀ i, A.HoloOn M₀ fun x => q x i) {W : Set X} (hWo : IsOpen W)
    (hWM : W ⊆ M₀) {U B : Set (Fin e → ℂ)} (hUo : IsOpen U) (hB : MeasurableSet B)
    (hBU : B ⊆ U) {s : (Fin e → ℂ) → X} (hsc : ContinuousOn s U)
    (hsU : ∀ u ∈ U, s u ∈ W ∧ q (s u) = u) (hsW : ∀ x ∈ W, q x ∈ U ∧ s (q x) = x)
    (g : (Fin e → ℂ) → ENNReal) :
    ∫⁻ y in ((A.chart j).target ∩ (A.chart j).symm ⁻¹' W) ∩ (q ∘ (A.chart j).symm) ⁻¹' B,
        ENNReal.ofReal (χ.χ j ((A.chart j).symm y)) *
          ENNReal.ofReal (‖LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) y :
            (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))‖ ^ 2) * g (q ((A.chart j).symm y)) =
      ∫⁻ u in B, ENNReal.ofReal (χ.χ j (s u)) * g u := by
  set φ := A.chart j with hφ
  set D := (φ.target ∩ φ.symm ⁻¹' W) ∩ (q ∘ φ.symm) ⁻¹' B with hD
  have hDm : MeasurableSet D := measurableSet_piece j hholo hWo hWM hB
  have hτ : ∀ y ∈ D, AnalyticAt ℂ (q ∘ φ.symm) y := fun y hy =>
    analyticAt_chart j hholo ⟨hy.1.1, hWM hy.1.2⟩
  have hder : ∀ y ∈ D, HasFDerivWithinAt (q ∘ φ.symm)
      ((fderiv ℂ (q ∘ φ.symm) y).restrictScalars ℝ) D y := fun y hy =>
    ((hτ y hy).differentiableAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have hinj : Set.InjOn (q ∘ φ.symm) D := by
    intro y hy y' hy' hyy
    have h1 : φ.symm y = φ.symm y' := by
      rw [← (hsW _ hy.1.2).2, ← (hsW _ hy'.1.2).2]
      exact congrArg s hyy
    rw [← φ.right_inv hy.1.1, ← φ.right_inv hy'.1.1, h1]
  set G : (Fin e → ℂ) → ENNReal := fun u => ENNReal.ofReal (χ.χ j (s u)) * g u with hG
  have hcv := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hDm hder hinj G
  set T := U ∩ s ⁻¹' φ.source with hT
  have hTo : IsOpen T := hsc.isOpen_inter_preimage hUo φ.open_source
  have himg : (q ∘ φ.symm) '' D = B ∩ T := by
    ext u
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hU := hsW _ hy.1.2
      refine ⟨hy.2, hU.1, ?_⟩
      show s (q (φ.symm y)) ∈ φ.source
      rw [hU.2]
      exact φ.map_target hy.1.1
    · rintro ⟨huB, huU, hus⟩
      have hus' : s u ∈ φ.source := hus
      refine ⟨φ (s u), ⟨⟨φ.map_source hus', ?_⟩, ?_⟩, ?_⟩
      · show φ.symm (φ (s u)) ∈ W
        rw [φ.left_inv hus']
        exact (hsU u (hBU huB)).1
      · show q (φ.symm (φ (s u))) ∈ B
        rw [φ.left_inv hus', (hsU u (hBU huB)).2]
        exact huB
      · show q (φ.symm (φ (s u))) = u
        rw [φ.left_inv hus', (hsU u (hBU huB)).2]
  have hrest : ∫⁻ u in B \ T, G u = 0 := by
    rw [setLIntegral_congr_fun (hB.diff hTo.measurableSet) (g := fun _ => 0) ?_, lintegral_zero]
    rintro u ⟨huB, huT⟩
    have hns : s u ∉ φ.source := fun h => huT ⟨hBU huB, h⟩
    have h0 : χ.χ j (s u) = 0 :=
      image_eq_zero_of_notMem_tsupport fun h => hns (χ.tsupport_subset j h)
    simp only [hG, h0, ENNReal.ofReal_zero, zero_mul]
  have hBT : ∫⁻ u in B, G u = ∫⁻ u in B ∩ T, G u := by
    rw [← lintegral_inter_add_sdiff G B hTo.measurableSet, hrest, add_zero]
  rw [hBT, ← himg, hcv]
  refine setLIntegral_congr_fun hDm fun y hy => ?_
  have hs : s (q (φ.symm y)) = φ.symm y := (hsW _ hy.1.2).2
  simp only [hG, degree_det_restrictScalars, Function.comp_apply]
  rw [hs, abs_of_nonneg (by positivity)]
  ring
end GroundTheory.Heights₂.Heights.FourB.CoverChartLIntegral
