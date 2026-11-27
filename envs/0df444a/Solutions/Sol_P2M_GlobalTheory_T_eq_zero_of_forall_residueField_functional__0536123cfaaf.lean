-- Prove2me | solution 1 for P2M_GlobalTheory_T_eq_zero_of_forall_residueField_functional__0536123cfaaf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:53:29.126125+00:00
-- url     : https://prove2.me/submissions/fa13a399-c77a-435f-a049-237ab605a370

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqZeroOfForallResidueFieldFunctional
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqZeroOfForallResidueFieldFunctionalStatement
import Theorems.Thm_GlobalTheory_eq_zero_of_forall_residueField_functional


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
theorem _root_.solution : ∀ (A M : Type) [CommRing A] [IsReduced A] [AddCommGroup M] [Module A M] [Module.Finite A M] [Module.Projective A M] (x : M), (∀ (p : Ideal A) [p.IsPrime] (l : M →ₗ[A] p.ResidueField), l x = 0) → x = 0 := by
  first | exact @GlobalTheory.eq_zero_of_forall_residueField_functional | exact GlobalTheory.eq_zero_of_forall_residueField_functional | (intros; apply GlobalTheory.eq_zero_of_forall_residueField_functional <;> assumption)
end _root_.GlobalTheory.T
