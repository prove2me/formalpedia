-- Prove2me | solution 1 for P2M_GlobalTheory_T_residue_degree_one_of_linear_mem__c7226ed25061
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:34:08.061563+00:00
-- url     : https://prove2.me/submissions/d06b889e-58da-47c9-a69e-19b66a9705fc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ResidueDegreeOneOfLinearMem
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ResidueDegreeOneOfLinearMemStatement
import Theorems.Thm_GlobalTheory_residue_degree_one_of_linear_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (P : Ideal B) [P.IsPrime] (θ : B) (D a b : A), (P.comap (algebraMap A B)).IsMaximal → (∀ y : B, ∃ u v : A, algebraMap A B D * y = algebraMap A B u + algebraMap A B v * θ) → algebraMap A B D ∉ P → algebraMap A B b ∉ P → algebraMap A B a + algebraMap A B b * θ ∈ P → ∀ y : B, ∃ u : A, y - algebraMap A B u ∈ P := by
  first | exact @GlobalTheory.residue_degree_one_of_linear_mem | exact GlobalTheory.residue_degree_one_of_linear_mem | (intros; apply GlobalTheory.residue_degree_one_of_linear_mem <;> assumption)
end _root_.GlobalTheory.T
