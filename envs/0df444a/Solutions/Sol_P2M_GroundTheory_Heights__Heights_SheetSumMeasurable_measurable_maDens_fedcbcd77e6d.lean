-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_measurable_maDens_fedcbcd77e6d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:32:13.067535+00:00
-- url     : https://prove2.me/submissions/6e27c6a6-62c1-45d9-964f-a4233d99df15

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsSheetMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GraphChartEventuallyEqSheet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_LogIntegrableOnOfLogIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable

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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.SheetSumMeasurable
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.SheetSumMeasurable
theorem _root_.solution {D : ℕ} (ψ : Fin D → (Fin D → ℂ) → ℝ) :
    Measurable (ReciprocityTheory.AnForm.maDens ψ) := by
  set M : ((Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ) → Matrix (Fin D) (Fin D) ℂ := fun H i j =>
    ((H (Pi.single i 1) (Pi.single j 1) +
        H (Complex.I • Pi.single i 1) (Complex.I • Pi.single j 1) : ℝ) +
      Complex.I * ((H (Pi.single i 1) (Complex.I • Pi.single j 1) -
        H (Complex.I • Pi.single i 1) (Pi.single j 1) : ℝ))) / 4 with hMdef
  have hM : Continuous M := continuous_pi fun i => continuous_pi fun j => by
    simp only [hMdef]
    fun_prop
  have hdisc : Continuous fun B : Fin D → Matrix (Fin D) (Fin D) ℂ =>
      (ReciprocityTheory.AnForm.mdisc B).re := by
    unfold ReciprocityTheory.AnForm.mdisc
    exact Complex.continuous_re.comp (continuous_const.mul (continuous_finsetSum _ fun S _ =>
      continuous_const.mul (Continuous.matrix_det (continuous_finsetSum _ fun k _ =>
        continuous_apply k))))
  have heq : ReciprocityTheory.AnForm.maDens ψ = fun z => (D.factorial : ℝ) * (2 / Real.pi) ^ D *
      (ReciprocityTheory.AnForm.mdisc fun k => M (fderiv ℝ (fderiv ℝ (ψ k)) z)).re := rfl
  rw [heq]
  exact measurable_const.mul ((hdisc.comp (continuous_pi fun k => hM.comp (continuous_apply k))).measurable.comp
    (measurable_pi_lambda _ fun k => measurable_fderiv ℝ _))
end GroundTheory.Heights₂.Heights.SheetSumMeasurable
