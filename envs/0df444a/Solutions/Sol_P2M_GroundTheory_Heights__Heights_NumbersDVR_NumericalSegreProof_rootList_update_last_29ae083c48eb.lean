-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_NumericalSegreProof_rootList_update_last_29ae083c48eb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:40:35.005864+00:00
-- url     : https://prove2.me/submissions/1078ed8b-2bd9-4d0f-8cfe-d09844791026

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumSymm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PNumericalSegre
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_NumericalSegreProof_rootList_succ_70d997e45c88

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.NumericalSegreProof
variable {K : Type*} [DecidableEq K]
omit [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.NumericalSegreProof
theorem _root_.solution {i : ℕ} (x : Fin (i + 1) → K → ℤ) (β : Fin (i + 1) → ℕ) :
    rootList x (Function.update β (Fin.last i) (β (Fin.last i) + 1)) =
      rootList x β ++ [x (Fin.last i)] := by
  have hinit : Fin.init (Function.update β (Fin.last i) (β (Fin.last i) + 1)) = Fin.init β := by
    funext j
    simp [Fin.init]
  rw [rootList_succ, rootList_succ x β, hinit, Function.update_self, List.replicate_succ',
    List.append_assoc]
end GroundTheory.Heights₂.Heights.NumbersDVR.NumericalSegreProof
