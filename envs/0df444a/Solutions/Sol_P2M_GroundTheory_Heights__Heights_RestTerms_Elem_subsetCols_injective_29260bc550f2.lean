-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Elem_subsetCols_injective_29260bc550f2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:51:17.026083+00:00
-- url     : https://prove2.me/submissions/ca191b4e-9ecb-4e09-a4aa-cf60ec7c0154

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
theorem _root_.solution {p : ℕ} (S : {s : Finset κ // s.card = p}) :
    Function.Injective (subsetCols S) := by
  intro i j h
  exact (S.1.equivFinOfCardEq S.2).symm.injective (Subtype.ext h)
end GroundTheory.Heights₂.Heights.RestTerms.Elem
