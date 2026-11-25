-- Prove2me | solution 1 for P2M_GlobalTheory_T_relIndex_oneUnits_mul_eq_card_quotient__e71c35adc924
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:34:04.522935+00:00
-- url     : https://prove2.me/submissions/0b1aefe9-251e-4056-8161-b689db8b82a5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_RelIndexOneUnitsMulEqCardQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_RelIndexOneUnitsMulEqCardQuotientStatement
import Theorems.Thm_GlobalTheory_CNorm_relIndex_oneUnits_mul_eq_card_quotient


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (O : Type) [CommRing O] [IsDomain O] (t s : O), t ≠ 0 → s ∣ t → Ideal.span {t} ≤ Ideal.jacobson (⊥ : Ideal O) → (oneUnits (s * t)).relIndex (oneUnits t) = Nat.card (O ⧸ Ideal.span {s}) := by
  first | exact @GlobalTheory.CNorm.relIndex_oneUnits_mul_eq_card_quotient | exact GlobalTheory.CNorm.relIndex_oneUnits_mul_eq_card_quotient | (intros; apply GlobalTheory.CNorm.relIndex_oneUnits_mul_eq_card_quotient <;> assumption)
end _root_.GlobalTheory.T
