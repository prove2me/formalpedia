-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.paU_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:30:13.137913+00:00
-- url     : https://prove2.me/submissions/2ec081a4-d2f1-43dc-8bb4-6588b08d904e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropABSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaThContinuous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_ExpNEllMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_paHf_contDiff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_paPF_contDiff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_paPoly_exists


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]
open Classical
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {q c : ℕ} (a : EuclideanSpace ℂ ι) {F : EuclideanSpace ℂ ι → ℂ}
    (hF : F ∈ paPoly c) : ContDiff ℂ (⊤ : ℕ∞) (paU q a F) := by
  obtain ⟨p, -, rfl⟩ := paPoly_exists hF
  unfold paU
  refine ContDiff.mul ?_ ((paPF_contDiff p).comp (contDiff_id.sub contDiff_const))
  exact Complex.contDiff_exp.comp ((contDiff_const.mul (paHf_contDiff a)).sub contDiff_const)
end ReciprocityTheory.ChartRestriction.G.I2
