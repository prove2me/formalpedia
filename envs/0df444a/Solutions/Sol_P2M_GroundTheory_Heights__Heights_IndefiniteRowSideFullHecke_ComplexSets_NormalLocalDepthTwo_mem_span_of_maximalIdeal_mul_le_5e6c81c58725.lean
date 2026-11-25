-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_NormalLocalDepthTwo_mem_span_of_maximalIdeal_mul_le_5e6c81c58725
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:31:50.70009+00:00
-- url     : https://prove2.me/submissions/fc60b7a1-831a-49bb-900a-c3e4de1048f9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalLocalDepthTwo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalLocalDepthTwo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open IsLocalRing RingTheory.Sequence
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace NormalLocalDepthTwo
theorem _root_.solution {B : Type*} [CommRing B] [IsLocalRing B]
    [IsNoetherianRing B] [IsDomain B] [IsIntegrallyClosed B] (hm : ¬ (maximalIdeal B).IsPrincipal)
    {x y : B} (hx : x ≠ 0) (hy : ∀ a ∈ maximalIdeal B, ∃ b, a * y = x * b) : ∃ c, y = x * c := by
  let K := FractionRing B
  by_cases h : ∀ a ∈ maximalIdeal B, ∀ b, a * y = x * b → b ∈ maximalIdeal B
  ·
    set u : K := algebraMap B K y / algebraMap B K x with hu
    have hxK : algebraMap B K x ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective B K)).mpr hx
    let N : Submodule B K := Submodule.map (Algebra.linearMap B K) (maximalIdeal B)
    have hmbot : maximalIdeal B ≠ ⊥ := fun h0 => hm (h0 ▸ ⟨⟨0, by simp⟩⟩)
    have hN : N ≠ ⊥ := by
      obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hmbot
      intro hN0
      have : algebraMap B K a ∈ N := Submodule.mem_map_of_mem ha
      rw [hN0, Submodule.mem_bot] at this
      exact ha0 ((map_eq_zero_iff _ (IsFractionRing.injective B K)).mp this)
    have hNfg : N.FG := (IsNoetherian.noetherian (maximalIdeal B)).map _
    have hstab : ∀ n ∈ N, u • n ∈ N := by
      rintro _ ⟨a, ha, rfl⟩
      obtain ⟨b, hb⟩ := hy a ha
      refine ⟨b, h a ha b hb, ?_⟩
      change algebraMap B K b = u * algebraMap B K a
      rw [hu, div_mul_eq_mul_div, eq_div_iff hxK, ← map_mul, ← map_mul]
      congr 1
      linear_combination -hb
    obtain ⟨c, hc⟩ := IsIntegrallyClosed.isIntegral_iff.mp
      (isIntegral_of_smul_mem_submodule N hN hNfg u hstab)
    refine ⟨c, IsFractionRing.injective B K ?_⟩
    rw [map_mul, hc, hu]
    exact (mul_div_cancel₀ _ hxK).symm
  ·
    push Not at h
    obtain ⟨a, ha, b, hab, hb⟩ := h
    have hbu : IsUnit b := by
      by_contra hb'
      exact hb ((mem_maximalIdeal b).mpr hb')
    by_cases hy0 : y = 0
    · exact ⟨0, by simp [hy0]⟩
    exfalso
    apply hm
    refine ⟨⟨a, le_antisymm ?_ ?_⟩⟩
    · intro a' ha'
      obtain ⟨b', hb'⟩ := hy a' ha'
      have hab' : a' * b = a * b' := mul_right_cancel₀ hy0 (by linear_combination b * hb' - b' * hab)
      refine Submodule.mem_span_singleton.mpr ⟨b' * ↑hbu.unit⁻¹, ?_⟩
      rw [smul_eq_mul, show b' * ↑hbu.unit⁻¹ * a = (a * b') * ↑hbu.unit⁻¹ by ring, ← hab', mul_assoc,
        hbu.mul_val_inv, mul_one]
    · rw [Ideal.submodule_span_eq, Ideal.span_le, Set.singleton_subset_iff]
      exact ha
end NormalLocalDepthTwo
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
