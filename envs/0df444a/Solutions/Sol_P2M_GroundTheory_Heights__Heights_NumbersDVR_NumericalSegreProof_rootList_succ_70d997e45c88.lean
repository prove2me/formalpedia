-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_NumericalSegreProof_rootList_succ_70d997e45c88
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:00:36.293414+00:00
-- url     : https://prove2.me/submissions/83fa64fe-b5c5-4404-98de-f2dd786b8a97

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumSymm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PNumericalSegre

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
theorem _root_.solution {i : ℕ} (x : Fin (i + 1) → K → ℤ) (α : Fin (i + 1) → ℕ) :
    rootList x α = rootList (fun j => x (Fin.castSucc j)) (Fin.init α) ++
      List.replicate (α (Fin.last i)) (x (Fin.last i)) := by
  unfold rootList
  rw [List.finRange_succ_last]
  simp [List.flatMap_append, Fin.init, List.flatMap_map]
end GroundTheory.Heights₂.Heights.NumbersDVR.NumericalSegreProof
