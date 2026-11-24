-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PtsSumMeasurable_measurable_maDensity_55cc86a52e7c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:48:54.882368+00:00
-- url     : https://prove2.me/submissions/4a678a9e-565e-45b8-889d-13aa4042deae

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PtsSumMeasurableA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Metric Filter Topology ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.PtsSumMeasurable
namespace GroundTheory.Heights₂.Heights.PtsSumMeasurable
theorem _root_.solution {D : ℕ} (φ : Fin D → (Fin D → ℂ) → ℝ) :
    Measurable (maDensity φ) := by
  set M : ((Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ) → Matrix (Fin D) (Fin D) ℂ := fun H i j =>
    ((H (Pi.single i 1) (Pi.single j 1) +
        H (Complex.I • Pi.single i 1) (Complex.I • Pi.single j 1) : ℝ) +
      Complex.I * ((H (Pi.single i 1) (Complex.I • Pi.single j 1) -
        H (Complex.I • Pi.single i 1) (Pi.single j 1) : ℝ))) / 4 with hMdef
  have hM : Continuous M := continuous_pi fun i => continuous_pi fun j => by
    simp only [hMdef]
    fun_prop
  have hdisc : Continuous fun B : Fin D → Matrix (Fin D) (Fin D) ℂ => (mixedDisc B).re := by
    unfold mixedDisc
    exact Complex.continuous_re.comp (continuous_const.mul (continuous_finsetSum _ fun S _ =>
      continuous_const.mul (Continuous.matrix_det (continuous_finsetSum _ fun k _ =>
        continuous_apply k))))
  have heq : maDensity φ = fun z => (D.factorial : ℝ) * (2 / Real.pi) ^ D *
      (mixedDisc fun k => M (fderiv ℝ (fderiv ℝ (φ k)) z)).re := rfl
  rw [heq]
  exact measurable_const.mul ((hdisc.comp (continuous_pi fun k => hM.comp (continuous_apply k))).measurable.comp
    (measurable_pi_lambda _ fun k => measurable_fderiv ℝ _))
end GroundTheory.Heights₂.Heights.PtsSumMeasurable
