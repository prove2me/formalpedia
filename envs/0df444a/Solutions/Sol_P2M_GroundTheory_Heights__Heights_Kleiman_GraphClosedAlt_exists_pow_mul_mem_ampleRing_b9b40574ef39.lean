-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_exists_pow_mul_mem_ampleRing_b9b40574ef39
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:45:02.782237+00:00
-- url     : https://prove2.me/submissions/84087e3c-17a6-4c2e-b4a7-d8b2d22e3e18

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GeneratedTwistSysZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PGraphClosedLocal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_chartRing_subset_ampleChart_3b053720cbdb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_ampleChart_mul_6b78bc19ad86
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_ampleChart_pow_c93b6f94709a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_xProd_ne_zero_4f1426ca3038
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_exists_pow_mul_mem_chartRing_a0e8b6aa2917

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
theorem _root_.solution (H : SubSystem S x Ω) (h b : Ω) (J : Chart x)
    (hb : b ∈ ampleRing H 1 h)
    (hbJ : ∀ I : Chart x, ∃ e : ℕ,
      b ^ e * (xProd I ^ J.1.card / xProd J ^ I.1.card) ∈ ampleChart H 1 h I)
    {c : Ω} (hc : c ∈ chartRing S x J) : ∃ e : ℕ, b ^ e * c ∈ ampleRing H 1 h := by
  classical
  have hloc : ∀ I : Chart x, ∃ e : ℕ, b ^ e * c ∈ ampleChart H 1 h I := by
    intro I
    obtain ⟨e₀, he₀⟩ := hbJ I
    have hcU : c ∈ chartRing S x (chartUnion I J) := chartRing_mono Finset.subset_union_right hc
    obtain ⟨e₁, he₁⟩ := exists_pow_mul_mem_chartRing I J hcU
    refine ⟨e₀ * e₁, ?_⟩
    have hρσ : (xProd I ^ J.1.card / xProd J ^ I.1.card) *
        (xProd J ^ I.1.card / xProd I ^ J.1.card) = 1 := by
      have := xProd_ne_zero I
      have := xProd_ne_zero J
      field_simp
    have : b ^ (e₀ * e₁) * c = (b ^ e₀ * (xProd I ^ J.1.card / xProd J ^ I.1.card)) ^ e₁ *
        ((xProd J ^ I.1.card / xProd I ^ J.1.card) ^ e₁ * c) := by
      calc b ^ (e₀ * e₁) * c = (b ^ e₀) ^ e₁ * ((xProd I ^ J.1.card / xProd J ^ I.1.card) *
          (xProd J ^ I.1.card / xProd I ^ J.1.card)) ^ e₁ * c := by
            rw [hρσ, one_pow, mul_one, pow_mul]
        _ = _ := by ring
    rw [this]
    exact ampleChart_mul H h I (ampleChart_pow H h I he₀ e₁)
      (chartRing_subset_ampleChart H h I he₁)
  choose f hf using hloc
  refine ⟨∑ I, f I, Set.mem_iInter.mpr fun I => ?_⟩
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le
    (Finset.single_le_sum (fun I _ => Nat.zero_le (f I)) (Finset.mem_univ I))
  have : b ^ (f I + k) * c = (b ^ f I * c) * b ^ k := by ring
  rw [hk, this]
  exact ampleChart_mul H h I (hf I) (ampleChart_pow H h I (Set.mem_iInter.mp hb I) k)
end GroundTheory.Heights₂.Heights.Kleiman.GraphClosedAlt
