-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_ContractRelevant_extend_zero_inj_2eeca3831901
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:52:42.07736+00:00
-- url     : https://prove2.me/submissions/ffe09668-f593-431b-b8c1-17659bd5847a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_ContractRelevant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers GroundTheory.Heights₂.Heights.FieldNumbers.ContractRelevant
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
namespace GroundTheory.Heights₂.Heights.FieldNumbers.ContractRelevant
theorem _root_.solution {K K' : Type*} {j : K → K'} (hj : Function.Injective j)
    {x y : K → ℕ} : Function.extend j x 0 = Function.extend j y 0 ↔ x = y :=
  ⟨fun h => funext fun k => by simpa [hj.extend_apply] using congrFun h (j k), fun h => h ▸ rfl⟩
end GroundTheory.Heights₂.Heights.FieldNumbers.ContractRelevant
