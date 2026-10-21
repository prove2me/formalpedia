-- Prove2me | solution 1 for PrivSeqLearn.QueryComplexity.coverNumber_mono
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T18:44:05.708195+00:00
-- url     : https://prove2.me/submissions/c2dfdaa2-da0e-4063-b477-1605972917b9

import Mathlib
import Definitions.Def_PrivSeqLearn_QueryComplexity_Setting

set_option autoImplicit false
open PrivSeqLearn.QueryComplexity

lemma psl_coverable_mono_set {δ : ℝ} {L : ℕ} {U V : Set ℝ} (hUV : U ⊆ V)
    (h : Coverable δ L V) : Coverable δ L U := by
  obtain ⟨a, b, hs, hl⟩ := h
  exact ⟨a, b, hUV.trans hs, hl⟩

lemma psl_bounded_coverable {δ : ℝ} (hδ : 0 < δ) {V : Set ℝ} (hV : Bornology.IsBounded V) :
    ∃ L, Coverable δ L V := by
  obtain ⟨R, hR⟩ := hV.subset_closedBall 0
  refine ⟨⌈2 * R / δ⌉₊ + 1, fun j => -R + (j : ℕ) * δ, fun j => -R + ((j : ℕ) + 1) * δ, ?_, ?_⟩
  · intro x hx
    have hx' := hR hx
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_le] at hx'
    obtain ⟨h1, h2⟩ := hx'
    have hpos : 0 ≤ (x + R) / δ := div_nonneg (by linarith) hδ.le
    set j := ⌊(x + R) / δ⌋₊ with hj
    have hjle : (j : ℝ) ≤ (x + R) / δ := Nat.floor_le hpos
    have hjlt : (x + R) / δ < j + 1 := Nat.lt_floor_add_one _
    have hjn : j < ⌈2 * R / δ⌉₊ + 1 := by
      have h3 : (x + R) / δ ≤ 2 * R / δ := by
        apply div_le_div_of_nonneg_right _ hδ.le; linarith
      have h4 : (j : ℝ) ≤ ⌈2 * R / δ⌉₊ := hjle.trans (h3.trans (Nat.le_ceil _))
      have : j ≤ ⌈2 * R / δ⌉₊ := by exact_mod_cast h4
      omega
    rw [Set.mem_iUnion]
    refine ⟨⟨j, hjn⟩, ?_, ?_⟩
    · have := (le_div_iff₀ hδ).1 hjle
      show -R + (j : ℝ) * δ ≤ x
      linarith
    · have := (div_lt_iff₀ hδ).1 hjlt
      show x ≤ -R + ((j : ℝ) + 1) * δ
      linarith
  · intro j
    show -R + ((j : ℕ) + 1) * δ - (-R + (j : ℕ) * δ) ≤ δ
    linarith

theorem solution (δ : ℝ) (L : ℕ) (U V : Set ℝ) (hδ : 0 < δ) (hUV : U ⊆ V)
    (hV : Bornology.IsBounded V) (hU : L ≤ coverNumber δ U) :
    L ≤ coverNumber δ V := by
  obtain ⟨L0, hL0⟩ := psl_bounded_coverable hδ hV
  have hne : {L | Coverable δ L V}.Nonempty := ⟨L0, hL0⟩
  have hmem : Coverable δ (sInf {L | Coverable δ L V}) V := Nat.sInf_mem hne
  have h2 : coverNumber δ U ≤ coverNumber δ V :=
    Nat.sInf_le (psl_coverable_mono_set hUV hmem)
  exact hU.trans h2
