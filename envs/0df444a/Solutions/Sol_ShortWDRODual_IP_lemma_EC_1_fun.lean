-- Prove2me | solution 1 for ShortWDRODual.IP.lemma_EC_1_fun
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T14:23:41.831203+00:00
-- url     : https://prove2.me/submissions/42dded94-06a5-4143-969b-0584fded7e8b

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_ShortWDRODual_IP_Setting

open MeasureTheory ModelRiskOT.Duality
open scoped ENNReal

open ShortWDRODual.IP in
theorem solution {X : Type*} [MeasurableSpace X] (φ : X × X → EReal)
    (hφtop : ∀ p, φ p ≠ ⊤) :
    DiagDomFun φ ↔ ∀ α : ℝ, DiagDomSet {p | (α : EReal) < φ p} := by
  constructor
  · rintro ⟨hm, hd⟩ α
    refine ⟨measurableSet_lt measurable_const hm, fun xh x h => ?_⟩
    exact lt_of_lt_of_le h (hd xh x)
  · intro h
    refine ⟨?_, fun xh x => ?_⟩
    · apply measurable_of_Ioi
      intro a
      induction a using EReal.rec with
      | bot =>
        have : φ ⁻¹' Set.Ioi ⊥ = ⋃ n : ℕ, {p | (((-(n : ℝ)) : ℝ) : EReal) < φ p} := by
          ext p
          simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_iUnion, Set.mem_setOf_eq]
          constructor
          · intro hp
            obtain ⟨r, -, hr⟩ := EReal.lt_iff_exists_real_btwn.mp hp
            refine ⟨⌈-r⌉₊, lt_of_le_of_lt ?_ hr⟩
            have : -r ≤ (⌈-r⌉₊ : ℝ) := Nat.le_ceil _
            exact_mod_cast (by linarith : -(⌈-r⌉₊ : ℝ) ≤ r)
          · rintro ⟨n, hn⟩
            exact lt_of_le_of_lt bot_le hn
        rw [this]
        exact MeasurableSet.iUnion (fun n => (h _).1)
      | coe r => exact (h r).1
      | top =>
        have : φ ⁻¹' Set.Ioi ⊤ = ∅ := by
          ext p; simp
        rw [this]; exact MeasurableSet.empty
    · by_contra hlt
      push_neg at hlt
      obtain ⟨r, h1, h2⟩ := EReal.lt_iff_exists_real_btwn.mp hlt
      have := (h r).2 xh x h2
      exact absurd this (not_lt.mpr h1.le)
