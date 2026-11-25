-- Prove2me | solution 1 for P2M_GlobalTheory_T_length_coker_lsmul_eq_length_ker_add_sum__275061a9a21e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:34:10.142218+00:00
-- url     : https://prove2.me/submissions/0433436c-5477-45de-9f8e-fc1bae61b011

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthCokerLsmulEqLengthKerAddSum
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthCokerLsmulEqLengthKerAddSumStatement
import Theorems.Thm_GlobalTheory_length_coker_lsmul_eq_length_ker_add_sum


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
theorem _root_.solution : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] (b : A) (P : Finset (PrimeSpectrum A)), (∀ p ∈ P, ringKrullDim (A ⧸ p.asIdeal) = 1 ∧ b ∉ p.asIdeal) → ∀ (M : Type) [AddCommGroup M] [Module A M] [Module.Finite A M], (∀ p ∈ Module.support A M, p ∈ P ∨ p.asIdeal = IsLocalRing.maximalIdeal A) → Module.length A (LinearMap.ker (LinearMap.lsmul A M b)) ≠ ⊤ ∧ Module.length A (M ⧸ LinearMap.range (LinearMap.lsmul A M b)) = Module.length A (LinearMap.ker (LinearMap.lsmul A M b)) + ∑ p ∈ P, Module.length (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M) * Module.length A (A ⧸ (p.asIdeal ⊔ Ideal.span {b})) := by
  first | exact @GlobalTheory.length_coker_lsmul_eq_length_ker_add_sum | exact GlobalTheory.length_coker_lsmul_eq_length_ker_add_sum | (intros; apply GlobalTheory.length_coker_lsmul_eq_length_ker_add_sum <;> assumption)
end _root_.GlobalTheory.T
