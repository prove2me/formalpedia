-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.MI.lintegral_upper
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:58:33.027613+00:00
-- url     : https://prove2.me/submissions/132f395f-0e60-4445-a81c-634beedf726b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfD
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfE
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_jacU_L__09c946809e4d
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_measurableSet_Cy
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_continuous_jacU
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_measurable_normSq_jacU
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_det_L__ne_86719920b537
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_jac__ne_71b40fef22b3

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open Matrix MeasureTheory
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI
theorem _root_.solution (β : ι → Matrix (Fin r) (Fin r) ℂ) (hβ : ∀ τ, (β τ).BlockTriangular id)
    (hd : ∀ τ b, β τ b b ≠ 0) :
    ∫⁻ y, ENNReal.ofReal (Complex.normSq (jacU y)) * (Cy ι r).indicator 1 (Lβ β y) =
      ENNReal.ofReal ((Complex.normSq (LinearMap.det (Lβ β)) * Complex.normSq (jacβ β))⁻¹) * K0 ι r := by
  set LR : (UpI ι r → ℂ) →ₗ[ℝ] (UpI ι r → ℂ) := (Lβ β).restrictScalars ℝ with hLR_def
  have hdet : LinearMap.det LR = Complex.normSq (LinearMap.det (Lβ β)) := by
    rw [hLR_def, LinearMap.det_restrictScalars, Algebra.norm_complex_apply]
  have hdn := det_Lβ_ne β hβ hd
  have hdR : LinearMap.det LR ≠ 0 := by
    rw [hdet]
    exact (Complex.normSq_pos.2 hdn).ne'
  have hjbp : 0 < Complex.normSq (jacβ β) := Complex.normSq_pos.2 (jacβ_ne β hd)
  set G : (UpI ι r → ℂ) → ENNReal := fun z =>
    ENNReal.ofReal (Complex.normSq (jacU z) / Complex.normSq (jacβ β)) * (Cy ι r).indicator 1 z with hG_def
  have hG : Measurable G :=
    (ENNReal.measurable_ofReal.comp
      ((Complex.continuous_normSq.comp continuous_jacU).measurable.div_const _)).mul
      (measurable_one.indicator measurableSet_Cy)
  have hLRm : Measurable LR := LR.continuous_of_finiteDimensional.measurable
  have hpt : ∀ y, ENNReal.ofReal (Complex.normSq (jacU y)) * (Cy ι r).indicator 1 (Lβ β y) = G (LR y) := by
    intro y
    have e : LR y = Lβ β y := rfl
    rw [hG_def]
    dsimp only
    rw [e, jacU_Lβ β hβ, map_mul, mul_div_cancel_left₀ _ hjbp.ne']
  have hint : ∫⁻ z, G z = ENNReal.ofReal ((Complex.normSq (jacβ β))⁻¹) * K0 ι r := by
    have e : ∀ z, G z = ENNReal.ofReal ((Complex.normSq (jacβ β))⁻¹) *
        (Cy ι r).indicator (fun z => ENNReal.ofReal (Complex.normSq (jacU z))) z := by
      intro z
      rw [hG_def]
      dsimp only
      by_cases hz : z ∈ Cy ι r
      · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, Pi.one_apply, mul_one, div_eq_mul_inv,
          ENNReal.ofReal_mul (Complex.normSq_nonneg _), mul_comm]
      · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, mul_zero, mul_zero]
    rw [lintegral_congr e, lintegral_const_mul _ (measurable_normSq_jacU.indicator measurableSet_Cy),
      lintegral_indicator measurableSet_Cy]
    rfl
  rw [lintegral_congr hpt, ← lintegral_map hG hLRm, Measure.map_linearMap_addHaar_eq_smul_addHaar _ hdR,
    lintegral_smul_measure, hint, smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg _), hdet,
    abs_of_nonneg (inv_nonneg.2 (Complex.normSq_nonneg _)), ← mul_inv]
end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
