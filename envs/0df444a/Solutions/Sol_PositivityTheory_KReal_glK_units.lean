-- Prove2me | solution 1 for PositivityTheory.KReal.glK_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:39:20.389178+00:00
-- url     : https://prove2.me/submissions/21354657-2937-4cc2-b968-5de653840873

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDefs
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCyc
import Theorems.Thm_PositivityTheory_KReal_eab_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace
open PositivityTheory PositivityTheory.KReal
variable {r s : ℕ}
namespace PositivityTheory.KReal
theorem _root_.solution {M : Type} [AddCommGroup M] [Module ℂ M] {act : Mat r s →ₗ[ℂ] Module.End ℂ M}
    (h : IsLie act) (a b c d : Ix r s) :
    units act a b * units act c d - units act c d * units act a b =
      (if b = c then units act a d else 0) - (if d = a then units act c b else 0) := by
  unfold units
  rw [h, eab_mul, eab_mul, map_sub]
  congr 1 <;> split_ifs <;> simp
end PositivityTheory.KReal
