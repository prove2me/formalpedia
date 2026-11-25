-- Prove2me | solution 1 for PI.WickFormula.Asm.xdeg_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:17:21.369937+00:00
-- url     : https://prove2.me/submissions/00392518-3030-41a7-9771-ae0bb6a3651a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_DeltaEqGdelta
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_XdegLeTotalDegree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open PI PI.WickFormula PI.WickFormula.Asm
namespace PI.WickFormula.Asm
theorem _root_.solution {r s : ℕ} (u v : Fin r ⊕ Fin s →₀ ℕ) : xdeg (u + v) = xdeg u + xdeg v := by
  simp [xdeg, Finset.sum_add_distrib]
end PI.WickFormula.Asm
