-- Prove2me | solution 1 for P2M_GlobalTheory_T_finsum_ord_mul_inertiaDeg_eq_finrank_mul_ord__1fcb71323d4a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:52:07.017119+00:00
-- url     : https://prove2.me/submissions/eba7f97d-5f88-4b6a-bb1c-a41cea33b7dd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinsumOrdMulInertiaDegEqFinrankMulOrd
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinsumOrdMulInertiaDegEqFinrankMulOrdStatement
import Theorems.Thm_GlobalTheory_finsum_ord_mul_inertiaDeg_eq_finrank_mul_ord


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
theorem _root_.solution : ∀ (A B : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A] [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B], Function.Injective (algebraMap A B) → ringKrullDim A = 1 → ∀ a : A, a ≠ 0 → ∑ᶠ Q ∈ {Q : PrimeSpectrum B | Q.asIdeal.comap (algebraMap A B) = IsLocalRing.maximalIdeal A}, ((Ring.ord (Localization.AtPrime Q.asIdeal) (algebraMap B _ (algebraMap A B a))).toNat : ℤ) * (Q.asIdeal.inertiaDeg A : ℤ) = (Module.finrank A B : ℤ) * ((Ring.ord A a).toNat : ℤ) := by
  first | exact @GlobalTheory.finsum_ord_mul_inertiaDeg_eq_finrank_mul_ord | exact GlobalTheory.finsum_ord_mul_inertiaDeg_eq_finrank_mul_ord | (intros; apply GlobalTheory.finsum_ord_mul_inertiaDeg_eq_finrank_mul_ord <;> assumption)
end _root_.GlobalTheory.T
