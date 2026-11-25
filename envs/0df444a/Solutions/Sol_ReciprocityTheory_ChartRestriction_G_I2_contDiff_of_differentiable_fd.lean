-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.contDiff_of_differentiable_fd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:38:07.554949+00:00
-- url     : https://prove2.me/submissions/1b885d48-0815-46c6-a61a-8fe7f9e23753

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContDiffOfDifferentiableFd
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_osgood


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    [FiniteDimensional ℂ W] {F : W → ℂ} (hF : Differentiable ℂ F) (k : ℕ) : ContDiff ℂ k F := by
  classical
  set e := Module.finrank ℂ W
  let L : W ≃L[ℂ] (Fin e → ℂ) := ContinuousLinearEquiv.ofFinrankEq (by simp [e])
  have hg : Differentiable ℂ (F ∘ L.symm) := hF.comp L.symm.differentiable
  have ha := ReciprocityTheory.AnForm.Osgood.osgood e Set.univ (F ∘ L.symm) isOpen_univ hg.differentiableOn
  have hc : ContDiff ℂ k (F ∘ L.symm) :=
    contDiff_iff_contDiffAt.2 fun x => (ha x (Set.mem_univ x)).contDiffAt
  have hF' : F = (F ∘ L.symm) ∘ L := by
    funext w
    simp
  rw [hF']
  exact hc.comp L.contDiff
end ReciprocityTheory.ChartRestriction.G.I2
