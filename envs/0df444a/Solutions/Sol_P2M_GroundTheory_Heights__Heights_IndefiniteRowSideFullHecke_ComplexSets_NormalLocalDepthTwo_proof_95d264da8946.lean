-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_NormalLocalDepthTwo_proof_95d264da8946
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:59:18.66894+00:00
-- url     : https://prove2.me/submissions/10f43969-f19e-44ee-b330-b427ac8eaf6c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalLocalDepthTwo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalLocalDepthTwo
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_NormalLocalDepthTwo_mem_span_of_maximalIdeal_mul_le_5e6c81c58725

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
theorem _root_.solution : NormalLocalDepthTwo.Statement := by
  intro B _ _ _ _ _
  by_cases hfield : IsField B
  · refine ⟨[], by simp, IsWeaklyRegular.nil B B, ?_⟩
    rw [ringKrullDim_eq_zero_of_isField hfield]
    simp
  have hmbot : maximalIdeal B ≠ ⊥ := isField_iff_maximalIdeal_eq.not.mp hfield
  obtain ⟨x, hxm, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hmbot
  have hxreg : IsSMulRegular B x := fun a b h => mul_left_cancel₀ hx0 h
  by_cases hp : (maximalIdeal B).IsPrincipal
  ·
    have : IsDiscreteValuationRing B := ((IsDiscreteValuationRing.TFAE B hfield).out 4 0).mp hp
    refine ⟨[x], by simpa using hxm,
      (isWeaklyRegular_cons_iff _ _ _).mpr ⟨hxreg, IsWeaklyRegular.nil _ _⟩, ?_⟩
    rw [IsDiscreteValuationRing.ringKrullDim_eq_one]
    simp

  have hreg : ∃ y ∈ maximalIdeal B, IsSMulRegular (QuotSMulTop x B) y := by
    by_contra hcon
    push Not at hcon
    have hsub : ((maximalIdeal B : Ideal B) : Set B) ⊆
        ⋃ p ∈ associatedPrimes B (QuotSMulTop x B), (p : Set B) := by
      rw [biUnion_associatedPrimes_eq_zero_divisors]
      intro y hy
      have h1 := hcon y hy
      rw [isSMulRegular_iff_right_eq_zero_of_smul] at h1
      push Not at h1
      obtain ⟨z, hz, hz0⟩ := h1
      exact ⟨z, hz0, hz⟩
    have hmem := (Ideal.subset_iUnion_iff_mem_of_isMaximal_of_finite
      (associatedPrimes.finite B (QuotSMulTop x B)) ⊥ ⊥
      (fun I hI _ _ => IsAssociatedPrime.isPrime hI) bot_ne_top bot_ne_top).mp hsub
    obtain ⟨-, z, hz⟩ := isAssociatedPrime_iff.mp hmem
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    have hyx : ∀ a ∈ maximalIdeal B, ∃ b, a * y = x * b := by
      intro a ha
      rw [hz, Submodule.mem_colon_singleton, Submodule.mem_bot, ← Submodule.Quotient.mk_smul,
        Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists] at ha
      obtain ⟨b, -, hb⟩ := ha
      exact ⟨b, by simpa [smul_eq_mul] using hb.symm⟩
    obtain ⟨c, hc⟩ := NormalLocalDepthTwo.mem_span_of_maximalIdeal_mul_le hp hx0 hyx
    have h1 : (1 : B) ∈ maximalIdeal B := by
      rw [hz, Submodule.mem_colon_singleton, one_smul, Submodule.mem_bot,
        Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists]
      exact ⟨c, trivial, by rw [hc, smul_eq_mul]⟩
    exact (maximalIdeal.isMaximal B).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  obtain ⟨y, hym, hy⟩ := hreg
  refine ⟨[x, y], ?_, ?_, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> assumption
  · exact (isWeaklyRegular_cons_iff _ _ _).mpr
      ⟨hxreg, (isWeaklyRegular_cons_iff _ _ _).mpr ⟨hy, IsWeaklyRegular.nil _ _⟩⟩
  · exact (min_le_left _ _).trans (by simp)
end NormalLocalDepthTwo
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
