-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_vandermondeOf_add_const_a9760dbf9300
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:14:11.456469+00:00
-- url     : https://prove2.me/submissions/314aca27-a47d-4ab3-98d5-0604d1022827

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_NumStandardTableEqCardMonotone
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PHookTableauCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open Finset
namespace GroundTheory.Heights₂.Heights.RestTerms
theorem _root_.solution {R : Type*} [CommRing R] {n : ℕ} (v : Fin n → R) (c : R) :
    vandermondeOf (fun j => v j + c) = vandermondeOf v := by
  unfold vandermondeOf
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  ring
end GroundTheory.Heights₂.Heights.RestTerms
