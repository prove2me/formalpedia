-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.FM.upper_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:58:19.104728+00:00
-- url     : https://prove2.me/submissions/fe156f88-cd14-4ba1-9d17-5404e969e1c0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FrameMeasStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FrameMeasStatementPfB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_FM_measurableSet_SR
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_det_L__ne_86719920b537
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_jacU_L__09c946809e4d
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_measurable_normSq_jacU


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.FM
open NumberField Matrix MeasureTheory Topology ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
  ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.FM
theorem _root_.solution (β : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (hβ : ∀ τ, (β τ).BlockTriangular id)
    (hd : ∀ τ b, β τ b b ≠ 0) (R0 : ℝ) :
    ∫⁻ y, ENNReal.ofReal (Complex.normSq (jacU y)) * (SR X R0).indicator 1 (Lβ β y) =
      ENNReal.ofReal ((Complex.normSq (LinearMap.det (Lβ β)) * Complex.normSq (jacβ β))⁻¹) * KR X R0 := by
  have hdet : LinearMap.det (Lβ β) ≠ 0 := det_Lβ_ne β hβ hd
  have hjac : jacβ β ≠ 0 := by
    unfold jacβ
    refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
    split_ifs
    · exact hd _ _
    · exact one_ne_zero
  have hnj : 0 < Complex.normSq (jacβ β) := Complex.normSq_pos.2 hjac
  have hnd : 0 < Complex.normSq (LinearMap.det (Lβ β)) := Complex.normSq_pos.2 hdet
  let Lr : (UpI X.Ψ r → ℂ) →ₗ[ℝ] (UpI X.Ψ r → ℂ) := (Lβ β).restrictScalars ℝ
  have hdetr : LinearMap.det Lr = Complex.normSq (LinearMap.det (Lβ β)) := by
    rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply]
  have hdetr0 : LinearMap.det Lr ≠ 0 := by rw [hdetr]; exact hnd.ne'
  have hmap := MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar
    (volume : Measure (UpI X.Ψ r → ℂ)) hdetr0
  have hSm : MeasurableSet (SR X R0) := measurableSet_SR X R0
  let c : ℝ≥0∞ := ENNReal.ofReal ((Complex.normSq (jacβ β))⁻¹)
  let G : (UpI X.Ψ r → ℂ) → ℝ≥0∞ := fun u =>
    ENNReal.ofReal (Complex.normSq (jacU u)) * c * (SR X R0).indicator 1 u
  have hG : Measurable G :=
    (measurable_normSq_jacU.mul_const c).mul (measurable_one.indicator hSm)
  have hLm : Measurable Lr := Lr.continuous_of_finiteDimensional.measurable
  have hpt : ∀ y, ENNReal.ofReal (Complex.normSq (jacU y)) * (SR X R0).indicator 1 (Lβ β y) =
      G (Lr y) := by
    intro y
    have e : ENNReal.ofReal (Complex.normSq (jacβ β * jacU y)) * c =
        ENNReal.ofReal (Complex.normSq (jacU y)) := by
      rw [Complex.normSq_mul, ← ENNReal.ofReal_mul (mul_nonneg hnj.le (Complex.normSq_nonneg _))]
      congr 1
      rw [mul_right_comm, mul_inv_cancel₀ hnj.ne', one_mul]
    show _ = ENNReal.ofReal (Complex.normSq (jacU (Lβ β y))) * c * (SR X R0).indicator 1 (Lβ β y)
    rw [jacU_Lβ β hβ y, e]
  have hGi : ∫⁻ u, G u = KR X R0 * c := by
    have h : G = (SR X R0).indicator (fun u => ENNReal.ofReal (Complex.normSq (jacU u)) * c) := by
      funext u
      simp only [G, Set.indicator]
      split_ifs <;> simp
    rw [h, lintegral_indicator hSm, lintegral_mul_const _ measurable_normSq_jacU]
    rfl
  calc ∫⁻ y, ENNReal.ofReal (Complex.normSq (jacU y)) * (SR X R0).indicator 1 (Lβ β y)
      = ∫⁻ y, G (Lr y) := lintegral_congr fun y => hpt y
    _ = ∫⁻ u, G u ∂(Measure.map Lr volume) := (lintegral_map hG hLm).symm
    _ = ENNReal.ofReal |(LinearMap.det Lr)⁻¹| * ∫⁻ u, G u := by
        rw [hmap, lintegral_smul_measure, smul_eq_mul]
    _ = _ := by
        rw [hGi, hdetr, abs_of_pos (inv_pos.2 hnd), mul_inv, ENNReal.ofReal_mul (inv_pos.2 hnd).le]
        ring
end ReciprocityTheory.ChartRestriction.G.AR.Up.FM
