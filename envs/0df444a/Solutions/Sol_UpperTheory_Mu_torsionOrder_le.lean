-- Prove2me | solution 1 for UpperTheory.Mu.torsionOrder_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:14:10.912732+00:00
-- url     : https://prove2.me/submissions/a002e6a7-6e7a-4cfd-8ab3-0ea91f16c2fd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_TorsionTotientBound
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RootsOfUnity_Monomial
import Theorems.Thm_Formalism_L2_SG_NGCut_TorsionTotientBound_torsionOrder_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open UpperTheory UpperTheory.Mu
variable {K : Type} [Field K] [NumberField K]
namespace UpperTheory.Mu
theorem _root_.solution (K : Type) [Field K] [NumberField K] : Units.torsionOrder K ≤ 2 * Module.finrank ℚ K ^ 2 :=
  Formalism.L2.SG.NGCut.TorsionTotientBound.torsionOrder_le K
end UpperTheory.Mu
