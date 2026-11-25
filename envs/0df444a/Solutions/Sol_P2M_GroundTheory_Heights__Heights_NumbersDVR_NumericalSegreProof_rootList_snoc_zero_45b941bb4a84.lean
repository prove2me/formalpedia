-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_NumericalSegreProof_rootList_snoc_zero_45b941bb4a84
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:40:33.579287+00:00
-- url     : https://prove2.me/submissions/a68041f7-9854-4b32-9d81-181ab494a0a0

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
theorem _root_.solution {i : ℕ} (x : Fin (i + 1) → K → ℤ) (α : Fin i → ℕ) :
    rootList x (Fin.snoc α 0) = rootList (fun j => x (Fin.castSucc j)) α := by
  rw [rootList_succ, Fin.init_snoc, Fin.snoc_last]
  simp
end GroundTheory.Heights₂.Heights.NumbersDVR.NumericalSegreProof
