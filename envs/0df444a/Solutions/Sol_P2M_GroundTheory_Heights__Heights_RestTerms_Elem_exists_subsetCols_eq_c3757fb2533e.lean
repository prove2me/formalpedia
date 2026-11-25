-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Elem_exists_subsetCols_eq_c3757fb2533e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:50:38.403624+00:00
-- url     : https://prove2.me/submissions/811e3865-e498-4092-8463-6a3f10832dd5

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
theorem _root_.solution {p : ℕ} (S : {s : Finset κ // s.card = p}) {k : κ}
    (hk : k ∈ S.1) : ∃ i, subsetCols S i = k :=
  ⟨S.1.equivFinOfCardEq S.2 ⟨k, hk⟩, by simp [subsetCols]⟩
end GroundTheory.Heights₂.Heights.RestTerms.Elem
