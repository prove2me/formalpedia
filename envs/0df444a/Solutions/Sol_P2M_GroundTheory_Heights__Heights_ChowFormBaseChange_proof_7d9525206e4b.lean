-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowFormBaseChange_proof_7d9525206e4b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:01:34.177215+00:00
-- url     : https://prove2.me/submissions/1c798e21-9a08-46e9-a2a1-5d5ad3b8d6fa

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Characterised
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LowerBoundConditional
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChowFormBaseChange
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isHomogIdeal_map_baf010c3c500
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isProjPrime_of_mem_support_fundCycle_dd2dcd3ea52a


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
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
namespace GroundTheory.Heights₂.Heights
namespace ChowFormBaseChange
theorem _root_.solution (hRad : RadicalBaseChange.Statement)
    (hExt : ChowFormExtend.Statement) (hRed : ChowFormReduced.Statement) :
    ChowFormBaseChange.Statement := by
  intro K _ _ n k I f σ hI hf
  have hJ : IsHomogIdeal (I.map (MvPolynomial.map σ)) := isHomogIdeal_map σ hI.isHomog
  refine ⟨fun W hW => isProjPrime_of_mem_support_fundCycle hJ hW, ?_⟩
  exact hRed ℂ n k _ _ hJ (hRad K ℂ σ (Fin n) I hI.isPrime.isRadical) (hExt K ℂ σ n k I f hf)
end ChowFormBaseChange
end GroundTheory.Heights₂.Heights
