-- Prove2me | solution 1 for PI.WickFormula.Asm.xdeg_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:17:25.07155+00:00
-- url     : https://prove2.me/submissions/f2e2d02c-0de5-4a4b-9b0f-856ee3e74de0

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
theorem _root_.solution {r s : ℕ} (i : Fin r) : xdeg (Finsupp.single (Sum.inl i : Fin r ⊕ Fin s) 1) = 1 := by
  simp [xdeg, Finsupp.single_apply]
end PI.WickFormula.Asm
