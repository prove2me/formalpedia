-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.setIntegral_parametrisation_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:52:45.711434+00:00
-- url     : https://prove2.me/submissions/476cbc74-f135-4cc4-a879-fb21d0043c4c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AInterpSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ABridgeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_MorseGenSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_PenMet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ExistsBoundIteratedFDerivCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory
open scoped ContDiff
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {J : Type} [Fintype J] {D : ℕ} {μ : Measure (J → ℂ)} {δ : ℝ}
    {γ' : (Fin D → ℂ) → J → ℂ} {ν' : (Fin D → ℂ) → ℝ}
    (hν' : IsDensityFor μ (Metric.ball 0 δ) γ' ν')
    {g : (J → ℂ) → ℝ} (hgm : Measurable g) (hg0 : IsDegZero g) (hgnn : ∀ z, 0 ≤ g z)
    (hgi : Integrable g μ) {h : (Fin D → ℂ) → ℝ} (hc : ContinuousOn h (Metric.ball 0 δ))
    (heq : ∀ y ∈ Metric.ball (0 : Fin D → ℂ) δ, h y = g (γ' y) * ν' y) :
    IntegrableOn h (Metric.ball 0 δ) ∧ ∫ y in Metric.ball (0 : Fin D → ℂ) δ, h y ≤ ∫ z, g z ∂μ := by
  obtain ⟨_, hpos, hden⟩ := hν'
  have hU : MeasurableSet (Metric.ball (0 : Fin D → ℂ) δ) := measurableSet_ball
  have hh0 : ∀ y ∈ Metric.ball (0 : Fin D → ℂ) δ, 0 ≤ h y := fun y hy => by
    rw [heq y hy]; exact mul_nonneg (hgnn _) (hpos y hy).le
  have hkey := hden g hgm hg0 hgnn
  have hlin : ∫⁻ y in Metric.ball (0 : Fin D → ℂ) δ, ENNReal.ofReal (h y) =
      ∫⁻ y in Metric.ball (0 : Fin D → ℂ) δ, ENNReal.ofReal (g (γ' y) * ν' y) :=
    setLIntegral_congr_fun hU (fun y hy => by rw [heq y hy])
  have hle : ∫⁻ y in Metric.ball (0 : Fin D → ℂ) δ, ENNReal.ofReal (h y) ≤ ∫⁻ z, ENNReal.ofReal (g z) ∂μ := by
    rw [hlin, ← hkey]
    exact setLIntegral_le_lintegral _ _
  have hgfin : ∫⁻ z, ENNReal.ofReal (g z) ∂μ < ⊤ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hgi (ae_of_all _ hgnn)]
    exact ENNReal.ofReal_lt_top
  have hmeas : AEStronglyMeasurable h (volume.restrict (Metric.ball (0 : Fin D → ℂ) δ)) :=
    hc.aestronglyMeasurable hU
  have hnn : 0 ≤ᵐ[volume.restrict (Metric.ball (0 : Fin D → ℂ) δ)] h := ae_restrict_of_forall_mem hU hh0
  have hint : IntegrableOn h (Metric.ball 0 δ) := by
    refine ⟨hmeas, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal hnn]
    exact lt_of_le_of_lt hle hgfin
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnn hmeas,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hgnn) hgi.aestronglyMeasurable]
  exact ENNReal.toReal_mono hgfin.ne hle
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
