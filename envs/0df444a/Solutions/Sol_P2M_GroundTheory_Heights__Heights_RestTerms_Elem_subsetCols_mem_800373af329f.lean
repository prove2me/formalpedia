-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Elem_subsetCols_mem_800373af329f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:51:19.093004+00:00
-- url     : https://prove2.me/submissions/f155a174-3ef2-46e2-9ebe-d46cecf9b665

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Pluecker

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
open GroundTheory.Heights₂.Heights.RestTerms
open Matrix Finset
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.RestTerms.Elem
variable {R : Type*} [CommRing R] {κ : Type*}
namespace GroundTheory.Heights₂.Heights.RestTerms.Elem
theorem _root_.solution {p : ℕ} (S : {s : Finset κ // s.card = p}) (i : Fin p) :
    subsetCols S i ∈ S.1 :=
  ((S.1.equivFinOfCardEq S.2).symm i).2
end GroundTheory.Heights₂.Heights.RestTerms.Elem
