-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_splitFracMap_mk_90d3ee9fcc29
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:07:26.223883+00:00
-- url     : https://prove2.me/submissions/8fd356be-29b3-484a-97e7-423d78fc34f7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsRename
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_ContractBlocksSplitPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PSplitRelDeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
variable {F : Type u} [Field F] {K K' : Type} (j : K ↪ K') {ι' : K' → Type}
  (P' : Ideal (MRing ι' F)) [P'.IsPrime]
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution (f : MRing (splitCoord j ι') F) :
    splitFracMap j P' (algebraMap _ _ (Ideal.Quotient.mk (splitPrime j P') f)) =
      algebraMap _ _ (Ideal.Quotient.mk P' (rename (splitVar j ι') f)) := by
  simp [splitFracMap, splitQuotToFrac]
  rfl
end GroundTheory.Heights₂.Heights.FieldNumbers
