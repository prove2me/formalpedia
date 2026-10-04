-- Prove2me | solution 1 for TeschlQM.KatoRellich.second_resolvent_formula
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T08:34:01.894046+00:00
-- url     : https://prove2.me/submissions/18b5c3b4-d83c-44d3-9a39-6f7c4cdc2a7e

import Mathlib
import Definitions.Def_TeschlQM_KatoRellich_resolvent

set_option autoImplicit false

open TeschlQM.KatoRellich in
theorem f7954fbb_resolvent_spec {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) (z : ℂ) (hz : z ∈ resolventSet A) :
    IsResolventAt A z (resolvent A z) := by
  have h' : ∃ R : H →L[ℂ] H, IsResolventAt A z R := hz
  unfold TeschlQM.KatoRellich.resolvent
  rw [dif_pos h']
  exact h'.choose_spec

open TeschlQM.KatoRellich in
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A B : H →ₗ.[ℂ] H) (hA : A.IsClosed) (hB : B.IsClosed)
    (hD : A.domain ≤ B.domain) (z : ℂ) (hzA : z ∈ resolventSet A)
    (hzAB : z ∈ resolventSet (A + B)) :
    (∀ φ : H, ∃ h : resolvent (A + B) z φ ∈ B.domain,
        resolvent (A + B) z φ - resolvent A z φ = -resolvent A z (B ⟨resolvent (A + B) z φ, h⟩)) ∧
      ∀ φ : H, ∃ h : resolvent A z φ ∈ B.domain,
        resolvent (A + B) z φ - resolvent A z φ = -resolvent (A + B) z (B ⟨resolvent A z φ, h⟩) := by
  obtain ⟨hA1, hA2⟩ := f7954fbb_resolvent_spec A z hzA
  obtain ⟨hS1, hS2⟩ := f7954fbb_resolvent_spec (A + B) z hzAB
  constructor
  · intro φ
    obtain ⟨hu, hφ⟩ := hS1 φ
    set u := resolvent (A + B) z φ with hu_def
    have huA : u ∈ A.domain := hu.1
    have huB : u ∈ B.domain := hu.2
    refine ⟨huB, ?_⟩
    have hsum : (A + B) ⟨u, hu⟩ = A ⟨u, huA⟩ + B ⟨u, huB⟩ :=
      LinearPMap.add_apply A B ⟨u, hu⟩
    rw [hsum] at hφ
    have key := hA2 ⟨u, huA⟩
    simp only at key
    have e : A ⟨u, huA⟩ - z • u = φ - B ⟨u, huB⟩ := by
      rw [← hφ]; abel
    rw [e, map_sub] at key
    conv_lhs => rw [← key]
    abel
  · intro φ
    obtain ⟨hv, hφ⟩ := hA1 φ
    set v := resolvent A z φ with hv_def
    have hvB : v ∈ B.domain := hD hv
    refine ⟨hvB, ?_⟩
    have hvAB : v ∈ (A + B).domain := ⟨hv, hvB⟩
    have hsum : (A + B) ⟨v, hvAB⟩ = A ⟨v, hv⟩ + B ⟨v, hvB⟩ :=
      LinearPMap.add_apply A B ⟨v, hvAB⟩
    have key := hS2 ⟨v, hvAB⟩
    simp only at key
    have e : (A + B) ⟨v, hvAB⟩ - z • v = φ + B ⟨v, hvB⟩ := by
      rw [hsum, ← hφ]; abel
    rw [e, map_add] at key
    conv_lhs => rw [← key]
    abel
