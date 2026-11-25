-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowlaSelberg_le_of_map_le_a6eb8b4ef036
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:06:03.585341+00:00
-- url     : https://prove2.me/submissions/c7705128-b10b-47d4-9871-325745df4adf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_PWIdealField
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowlaSelberg_isIntegral_of_map_5350c19fe2cc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ChowlaSelberg
open NumberField
noncomputable section
namespace GroundTheory.Heights₂.Heights.ChowlaSelberg
theorem _root_.solution {F F' : Type*} [Field F] [NumberField F] [Field F'] [NumberField F']
    (j : F →+* F') {A B : Ideal (𝓞 F)} (hB : B ≠ ⊥)
    (h : A.map (RingOfIntegers.mapRingHom j) ≤ B.map (RingOfIntegers.mapRingHom j)) : A ≤ B := by
  obtain ⟨b, hbB, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hB
  obtain ⟨B', hB'⟩ : B ∣ Ideal.span {b} :=
    Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hbB)
  have hB'0 : B' ≠ 0 := by
    rintro rfl
    rw [mul_zero, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] at hB'
    exact hb0 hB'
  have key : A * B' ≤ B * B' := by
    rw [← hB', Ideal.mul_le]
    intro x hx y hy
    have hm : RingOfIntegers.mapRingHom j (x * y) ∈
        (Ideal.span {b}).map (RingOfIntegers.mapRingHom j) := by
      rw [hB', Ideal.map_mul, map_mul]
      exact Ideal.mul_mem_mul (h (Ideal.mem_map_of_mem _ hx)) (Ideal.mem_map_of_mem _ hy)
    rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at hm
    obtain ⟨z, hz⟩ := hm
    have hbF : (b : F) ≠ 0 := by
      intro h0
      exact hb0 (RingOfIntegers.ext (by simpa using h0))
    have hz' : (z : F') * j (b : F) = j ((x * y : 𝓞 F) : F) := by
      have := congrArg (fun t : 𝓞 F' ↦ (t : F')) hz
      simpa using this
    have himg : j (((x * y : 𝓞 F) : F) / (b : F)) = (z : F') := by
      rw [map_div₀, ← hz', mul_div_assoc, div_self ((map_ne_zero j).2 hbF), mul_one]
    have hq : IsIntegral ℤ (((x * y : 𝓞 F) : F) / (b : F)) := by
      apply isIntegral_of_map j
      rw [himg]
      exact RingOfIntegers.isIntegral_coe z
    rw [Ideal.mem_span_singleton']
    refine ⟨⟨_, hq⟩, RingOfIntegers.ext ?_⟩
    show ((x * y : 𝓞 F) : F) / (b : F) * (b : F) = ((x * y : 𝓞 F) : F)
    rw [div_mul_cancel₀ _ hbF]
  have hdvd : B * B' ∣ A * B' := Ideal.dvd_iff_le.2 key
  exact Ideal.dvd_iff_le.1 ((mul_dvd_mul_iff_right hB'0).1 hdvd)
end GroundTheory.Heights₂.Heights.ChowlaSelberg
