-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_exists_pow_mul_mem_chartRing_a0e8b6aa2917
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:30:53.225926+00:00
-- url     : https://prove2.me/submissions/8e3f67ac-7dab-4588-bde9-ceab7999981f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GeneratedTwistSysZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PGraphClosedLocal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_exists_pow_mul_ratio_mem_e076d5106805

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
theorem _root_.solution (I J : Chart x) {z : Ω}
    (hz : z ∈ chartRing S x (chartUnion I J)) : ∃ e : ℕ,
    (xProd J ^ I.1.card / xProd I ^ J.1.card) ^ e * z ∈ chartRing S x I := by
  set σ := xProd J ^ I.1.card / xProd I ^ J.1.card
  obtain ⟨i₀, hi₀⟩ := I.2.1
  have hw : x i₀ ≠ 0 := (mem_support x).mp (I.2.2 hi₀)
  have hmon : ∀ s ∈ monos (S := S) (I.1 ∪ J.1), ∃ (e d : ℕ), s.IsHomogeneous d ∧
      σ ^ e * (x i₀ ^ d / aeval x s) ∈ chartRing S x I := by
    intro s hs
    induction hs using Submonoid.closure_induction with
    | mem a ha =>
      obtain ⟨i, hi, rfl⟩ := ha
      obtain ⟨e, he⟩ := exists_pow_mul_ratio_mem (S := S) I J hi₀ (i := i) (by exact_mod_cast hi)
      exact ⟨e, 1, isHomogeneous_X S i, by rw [pow_one, aeval_X]; exact he⟩
    | one => exact ⟨0, 0, isHomogeneous_one _ _, by simp⟩
    | mul a b _ _ ha hb =>
      obtain ⟨e₁, d₁, had, hae⟩ := ha
      obtain ⟨e₂, d₂, hbd, hbe⟩ := hb
      refine ⟨e₁ + e₂, d₁ + d₂, had.mul hbd, ?_⟩
      have : σ ^ (e₁ + e₂) * (x i₀ ^ (d₁ + d₂) / aeval x (a * b)) =
          (σ ^ e₁ * (x i₀ ^ d₁ / aeval x a)) * (σ ^ e₂ * (x i₀ ^ d₂ / aeval x b)) := by
        rw [map_mul, pow_add, pow_add]; ring
      rw [this]
      exact mul_mem hae hbe
  obtain ⟨f, s, d, hs, hf, hsd, rfl⟩ := hz
  obtain ⟨e, d', hsd', hmem⟩ := hmon s hs
  have hs0 : aeval x s ≠ 0 := eval_ne_zero_of_mem_monos (chartUnion I J) hs
  have hsne : s ≠ 0 := fun h => hs0 (by rw [h, map_zero])
  have hdd : d' = d := hsd'.inj_right hsd hsne
  subst hdd
  have hf' : aeval x f / x i₀ ^ d' ∈ chartRing S x I :=
    ⟨f, X i₀ ^ d', d', pow_mem (X_mem_monos hi₀) d', hf, isHomogeneous_X_pow i₀ d', by simp⟩
  refine ⟨e, ?_⟩
  have : σ ^ e * (aeval x f / aeval x s) = (aeval x f / x i₀ ^ d') * (σ ^ e * (x i₀ ^ d' / aeval x s)) := by
    field_simp
  rw [this]
  exact mul_mem hf' hmem
end GroundTheory.Heights₂.Heights.Kleiman.GraphClosedAlt
