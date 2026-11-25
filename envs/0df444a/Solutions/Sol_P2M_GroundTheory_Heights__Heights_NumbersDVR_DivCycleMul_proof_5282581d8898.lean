-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_DivCycleMul_proof_5282581d8898
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:53:26.332975+00:00
-- url     : https://prove2.me/submissions/2e655645-69ea-43af-b6f0-467bdae9d1ab

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_length_localizedQuot_sup_span_mul_9bb1c97ab66a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_length_localizedQuot_ne_top_a831a4f25617
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_minimalPrimes_sup_span_mul_4461e376663a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_divCycle_eq_toNat_multAt_3727a3dc8d68

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
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace DivCycleMul
theorem _root_.solution : DivCycleMul.Statement := by
  intro R _ _ K _ ι _ P x y hP hx hy
  funext W
  have hxy : x * y ∉ P := fun h => (hP.mem_or_mem h).elim hx hy
  by_cases hrel : IsRelevant W
  swap
  · simp only [Pi.add_apply]
    unfold divCycle
    rw [dif_neg (fun h => hrel h.2), dif_neg (fun h => hrel h.2), dif_neg (fun h => hrel h.2),
      add_zero]
  by_cases hm : W ∈ (P ⊔ Ideal.span {x * y}).minimalPrimes
  · have hW : W.IsPrime := hm.1.1
    have hxle : P ⊔ Ideal.span {x * y} ≤ P ⊔ Ideal.span {x} :=
      sup_le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr
        (Ideal.mul_mem_right y _ (Ideal.mem_span_singleton_self x))) P
    have hyle : P ⊔ Ideal.span {x * y} ≤ P ⊔ Ideal.span {y} :=
      sup_le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr
        (Ideal.mul_mem_left _ x (Ideal.mem_span_singleton_self y))) P
    simp only [Pi.add_apply]
    rw [divCycle_eq_toNat_multAt (x * y) (x * y) hm hrel le_rfl,
      divCycle_eq_toNat_multAt x (x * y) hm hrel hxle,
      divCycle_eq_toNat_multAt y (x * y) hm hrel hyle]
    have htop := length_localizedQuot_ne_top _ W hm
    have hadd := length_localizedQuot_sup_span_mul P W y hx
    unfold multAt
    rw [hadd] at htop ⊢
    rw [ENat.toNat_add (WithTop.add_ne_top.mp htop).1 (WithTop.add_ne_top.mp htop).2]
    push_cast
    ring
  · simp only [Pi.add_apply]
    unfold divCycle
    have hnx : ¬ W ∈ (P ⊔ Ideal.span {x}).minimalPrimes :=
      fun h => hm (mem_minimalPrimes_sup_span_mul hy h)
    have hny : ¬ W ∈ (P ⊔ Ideal.span {y}).minimalPrimes :=
      fun h => hm (mul_comm y x ▸ mem_minimalPrimes_sup_span_mul hx h)
    rw [dif_neg (fun h => hm h.1), dif_neg (fun h => hnx h.1), dif_neg (fun h => hny h.1), add_zero]
end DivCycleMul
end GroundTheory.Heights₂.Heights.NumbersDVR
