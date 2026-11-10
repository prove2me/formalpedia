-- Prove2me | solution 1 for RiskSharingProjects.TimeDependent.lemma_2_dominant_strategy
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-10T03:22:17.628633+00:00
-- url     : https://prove2.me/submissions/95eb3c88-17f7-45fc-b3f3-34d8bc557394

import Mathlib
import Definitions.Def_RiskSharingProjects_TimeDependent_Action
import Definitions.Def_RiskSharingProjects_TimeDependent_supplierPayoff
import Definitions.Def_RiskSharingProjects_TimeDependent_manufacturerBestResponses
import Definitions.Def_RiskSharingProjects_TimeDependent_Condition2

namespace Aux_RiskSharing_l2

open RiskSharingProjects.TimeDependent

theorem M_val (s p q : ℝ) :
    manufacturerPayoff s p q Action.keep Action.keep = 0 ∧
    manufacturerPayoff s p q Action.keep Action.delay = s - p ∧
    manufacturerPayoff s p q Action.delay Action.keep = 0 - p ∧
    manufacturerPayoff s p q Action.delay Action.delay = s - (p + q) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    first
      | rfl
      | simp [manufacturerPayoff, projectDelay, delayPenalty]

theorem S_val (s p q : ℝ) :
    supplierPayoff s p q Action.keep Action.keep = 0 ∧
    supplierPayoff s p q Action.keep Action.delay = 0 - p ∧
    supplierPayoff s p q Action.delay Action.keep = s - p ∧
    supplierPayoff s p q Action.delay Action.delay = s - (p + q) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    first
      | rfl
      | simp [supplierPayoff, projectDelay, delayPenalty]

end Aux_RiskSharing_l2

open RiskSharingProjects.TimeDependent in
theorem solution (s1 s0 p11 p21 p10 p20 : ℝ)
    (hC2 : Condition2 s1 s0 p11 p21 p10 p20) :
    (s0 < p10 → ∀ a1, manufacturerBestResponses s0 p10 p20 a1 = {Action.keep}) ∧
    (p20 < s0 → ∀ a1, manufacturerBestResponses s0 p10 p20 a1 = {Action.delay}) ∧
    (0 < s1 → p11 < p21 → p21 < s1 →
      ∀ θ : ℝ × ℝ × ℝ, θ.2.1 < θ.2.2 → ∀ σ : Action → Action,
        (∀ a, σ a ∈ manufacturerBestResponses θ.1 θ.2.1 θ.2.2 a) →
        supplierPayoff s1 p11 p21 Action.keep (σ Action.keep) <
          supplierPayoff s1 p11 p21 Action.delay (σ Action.delay)) := by
  obtain ⟨⟨-, -⟩, -, -, h1020⟩ := hC2
  obtain ⟨mKK, mKD, mDK, mDD⟩ := Aux_RiskSharing_l2.M_val s0 p10 p20
  refine ⟨fun hs a1 => ?_, fun hs a1 => ?_, ?_⟩
  · ext a0
    simp only [manufacturerBestResponses, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro h
      cases a0
      · rfl
      · exfalso
        have := h Action.keep
        cases a1
        · rw [mKK, mKD] at this; linarith
        · rw [mDK, mDD] at this; linarith
    · rintro rfl b
      cases a1 <;> cases b
      · exact le_rfl
      · rw [mKK, mKD]; linarith
      · exact le_rfl
      · rw [mDK, mDD]; linarith
  · ext a0
    simp only [manufacturerBestResponses, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro h
      cases a0
      · exfalso
        have := h Action.delay
        cases a1
        · rw [mKK, mKD] at this; linarith
        · rw [mDK, mDD] at this; linarith
      · rfl
    · rintro rfl b
      cases a1 <;> cases b
      · rw [mKK, mKD]; linarith
      · exact le_rfl
      · rw [mDK, mDD]; linarith
      · exact le_rfl
  · intro hs1 hp hps θ hθ σ hσ
    obtain ⟨t0, t1, t2⟩ := θ
    simp only at hθ hσ
    obtain ⟨nKK, nKD, nDK, nDD⟩ := Aux_RiskSharing_l2.M_val t0 t1 t2
    obtain ⟨sKK, sKD, sDK, sDD⟩ := Aux_RiskSharing_l2.S_val s1 p11 p21
    have hk := hσ Action.keep
    have hd := hσ Action.delay
    simp only [manufacturerBestResponses, Set.mem_setOf_eq] at hk hd
    cases hdv : σ Action.delay
    · rw [hdv] at hd
      cases hkv : σ Action.keep
      · rw [sKK, sDK]; linarith
      · rw [sKD, sDK]; linarith
    · rw [hdv] at hd
      have h2 := hd Action.keep
      rw [nDK, nDD] at h2
      cases hkv : σ Action.keep
      · rw [hkv] at hk
        have h3 := hk Action.delay
        rw [nKK, nKD] at h3
        linarith
      · rw [sKD, sDD]; linarith
