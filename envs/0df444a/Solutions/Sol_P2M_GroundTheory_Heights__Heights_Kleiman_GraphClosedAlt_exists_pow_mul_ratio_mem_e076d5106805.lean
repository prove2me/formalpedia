-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_exists_pow_mul_ratio_mem_e076d5106805
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:20:58.991877+00:00
-- url     : https://prove2.me/submissions/bcc514fa-0ff1-4bf2-a180-ce1aebf6973f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GeneratedTwistSysZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PGraphClosedLocal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_xProd_ne_zero_4f1426ca3038
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_div_mem_chartRing_d354e0157f48

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.GraphClosedAlt
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.GraphClosedAlt
theorem _root_.solution (I J : Chart x) {i₀ : Fin (N + 1)} (hi₀ : i₀ ∈ I.1)
    {i : Fin (N + 1)} (hi : i ∈ I.1 ∪ J.1) : ∃ e : ℕ,
    (xProd J ^ I.1.card / xProd I ^ J.1.card) ^ e * (x i₀ / x i) ∈ chartRing S x I := by
  by_cases hiI : i ∈ I.1
  · exact ⟨0, by rw [pow_zero, one_mul]; exact div_mem_chartRing I i₀ hiI⟩
  have hiJ : i ∈ J.1 := (Finset.mem_union.mp hi).resolve_left hiI
  refine ⟨1, ?_⟩
  have hw : x i₀ ≠ 0 := (mem_support x).mp (I.2.2 hi₀)
  have hxi : x i ≠ 0 := (mem_support x).mp (J.2.2 hiJ)
  have hQ : xProd I ≠ 0 := xProd_ne_zero I
  obtain ⟨m, hm⟩ : ∃ m, I.1.card = m + 1 := ⟨I.1.card - 1, (Nat.succ_pred_eq_of_pos I.2.1.card_pos).symm⟩
  obtain ⟨c, hc⟩ : ∃ c, J.1.card = c + 1 := ⟨J.1.card - 1, (Nat.succ_pred_eq_of_pos J.2.1.card_pos).symm⟩
  have hce : (J.1.erase i).card = c := by rw [Finset.card_erase_of_mem hiJ, hc]; rfl
  set P := ∏ j ∈ J.1.erase i, x j with hP
  have hJP : xProd J = x i * P := (Finset.mul_prod_erase J.1 x hiJ).symm
  have hprodI : ∏ i' ∈ I.1, (x i₀ / x i') = x i₀ ^ (m + 1) / xProd I := by
    rw [Finset.prod_div_distrib, Finset.prod_const, hm]; rfl
  have hprodJ : ∏ j ∈ J.1.erase i, (x j / x i₀) = P / x i₀ ^ c := by
    rw [Finset.prod_div_distrib, Finset.prod_const, hce]
  have key : (xProd J ^ I.1.card / xProd I ^ J.1.card) ^ 1 * (x i₀ / x i) =
      (x i / x i₀) ^ m * (∏ j ∈ J.1.erase i, (x j / x i₀)) ^ (m + 1) *
        (∏ i' ∈ I.1, (x i₀ / x i')) ^ (c + 1) := by
    rw [hprodI, hprodJ, hJP, hm, hc, pow_one]
    simp only [div_pow, mul_pow, ← pow_mul]
    field_simp
    ring
  rw [key]
  refine mul_mem (mul_mem (pow_mem (div_mem_chartRing I i hi₀) m)
    (pow_mem (prod_mem fun j _ => div_mem_chartRing I j hi₀) _))
    (pow_mem (prod_mem fun i' hi' => div_mem_chartRing I i₀ hi') _)
end GroundTheory.Heights₂.Heights.Kleiman.GraphClosedAlt
