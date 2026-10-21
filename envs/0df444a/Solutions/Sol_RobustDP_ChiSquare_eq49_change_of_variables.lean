-- Prove2me | solution 1 for RobustDP.ChiSquare.eq49_change_of_variables
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T02:34:07.901703+00:00
-- url     : https://prove2.me/submissions/f0c82582-82a4-4d49-8915-0c7c27ce66d3

import Mathlib
import Definitions.Def_RobustDP_ChiSquare_Moments
import Definitions.Def_RobustDP_ChiSquare_ChiSqSet

set_option autoImplicit false
open RobustDP.ChiSquare

theorem solution {S : Type*} [Fintype S] (q : S → ℝ)
    (hq : q ∈ stdSimplex ℝ S) (hq_pos : ∀ s, 0 < q s) (t : ℝ) (v : S → ℝ) :
    (∀ p : S → ℝ, p ∈ chiSqSet q t ↔
      ((∑ s, (p s - q s) ^ 2 / q s ≤ t) ∧ (∑ s, (p s - q s) = 0) ∧ ∀ s, -q s ≤ p s - q s)) ∧
    ∀ val : ℝ,
      IsLeast ((fun p => expect p v) '' chiSqSet q t) val ↔
        IsLeast ((fun y : S → ℝ => ∑ s, y s * v s) ''
            {y : S → ℝ | (∑ s, y s ^ 2 / q s ≤ t) ∧ (∑ s, y s = 0) ∧ ∀ s, -q s ≤ y s})
          (val - expect q v) := by
  have hmem : ∀ p : S → ℝ, p ∈ chiSqSet q t ↔
      ((∑ s, (p s - q s) ^ 2 / q s ≤ t) ∧ (∑ s, (p s - q s) = 0) ∧ ∀ s, -q s ≤ p s - q s) := by
    intro p
    simp only [chiSqSet, chiSqDist, Set.mem_setOf_eq, stdSimplex]
    constructor
    · rintro ⟨⟨h0, h1⟩, h2⟩
      refine ⟨h2, ?_, fun s => by linarith [h0 s]⟩
      rw [Finset.sum_sub_distrib, h1, hq.2]; simp
    · rintro ⟨h2, h1, h0⟩
      refine ⟨⟨fun s => by linarith [h0 s], ?_⟩, h2⟩
      have := h1
      rw [Finset.sum_sub_distrib, hq.2] at this
      linarith
  refine ⟨hmem, ?_⟩
  intro val
  have hE : ∀ y : S → ℝ, expect (y + q) v = (∑ s, y s * v s) + expect q v := by
    intro y
    simp only [expect, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  constructor
  · rintro ⟨⟨p, hp, hpv⟩, hlb⟩
    refine ⟨⟨p - q, (hmem p).1 hp, ?_⟩, ?_⟩
    · have := hE (p - q)
      simp only [sub_add_cancel] at this
      simp only at hpv ⊢
      linarith
    · rintro _ ⟨y, hy, rfl⟩
      have hp' : (y + q) ∈ chiSqSet q t := by
        rw [hmem]
        simpa using hy
      have := hlb ⟨y + q, hp', rfl⟩
      simp only at this
      rw [hE] at this
      linarith
  · rintro ⟨⟨y, hy, hyv⟩, hlb⟩
    have hp' : (y + q) ∈ chiSqSet q t := by
      rw [hmem]
      simpa using hy
    refine ⟨⟨y + q, hp', ?_⟩, ?_⟩
    · simp only at hyv ⊢
      rw [hE]; linarith
    · rintro _ ⟨p, hp, rfl⟩
      have := hlb ⟨p - q, (hmem p).1 hp, rfl⟩
      have h2 := hE (p - q)
      simp only [sub_add_cancel] at h2
      simp only at this ⊢
      linarith
