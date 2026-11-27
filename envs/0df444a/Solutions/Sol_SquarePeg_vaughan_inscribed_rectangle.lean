-- Prove2me | solution 1 for SquarePeg.vaughan_inscribed_rectangle
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-26T22:16:19.209126+00:00
-- url     : https://prove2.me/submissions/1aaf29fe-b123-432d-b6fc-eb7ddd410519
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SchoenfliesCurveCore
import Definitions.Def_SquarePeg_shapes
import Definitions.Def_SquarePeg_classes
import Definitions.Def_SquarePeg_similarity
import Theorems.Thm_LefebvreVariations_moebius_band_half_space_embedding

set_option autoImplicit false

open Schoenflies SquarePeg Set

/-! The variation, verbatim (the only open step of this file). -/

/-- A periodic parametrization of a Jordan curve. -/
private structure PLoop (C : Set Plane) (g : ℝ → Plane) : Prop where
  cont : Continuous g
  per : ∀ t, g (t + 1) = g t
  mem : ∀ t, g t ∈ C
  inj : ∀ s t, g s = g t → |s - t| < 1 → s = t

private lemma ploop_of_jordan (C : Set Plane) (hC : IsJordanCurve C) :
    ∃ g : ℝ → Plane, PLoop C g := by
  obtain ⟨f, hf, rfl⟩ := hC
  refine ⟨f ∘ Int.fract, ⟨?_, ?_, ?_, ?_⟩⟩
  · exact ContinuousOn.comp_fract'' hf.continuousOn hf.closes
  · intro t; simp [Int.fract_add_one]
  · intro t
    exact ⟨Int.fract t, ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩, rfl⟩
  · intro s t hst hlt
    have h1 : Int.fract s = Int.fract t :=
      hf.injOn ⟨Int.fract_nonneg s, Int.fract_lt_one s⟩
        ⟨Int.fract_nonneg t, Int.fract_lt_one t⟩ hst
    obtain ⟨z, hz⟩ := Int.fract_eq_fract.mp h1
    rw [hz] at hlt
    have : z = 0 := by
      have h2 : |(z : ℝ)| < 1 := hlt
      rw [abs_lt] at h2
      have h3 : (-1 : ℤ) < z := by exact_mod_cast h2.1
      have h4 : z < 1 := by exact_mod_cast h2.2
      omega
    rw [this] at hz; simp at hz; linarith

private lemma ploop_int {C : Set Plane} {g : ℝ → Plane} (h : PLoop C g) (x : ℝ) (n : ℤ) :
    g (x + n) = g x := by
  have hp : Function.Periodic g 1 := h.per
  simpa using (hp.int_mul n) x

/-- Two parameters with the same point differ by an integer. -/
private lemma ploop_eq_int {C : Set Plane} {g : ℝ → Plane} (h : PLoop C g) (s t : ℝ)
    (hst : g s = g t) : ∃ n : ℤ, t = s + n := by
  have h1 : g (s + Int.fract (t - s)) = g s := by
    have : s + Int.fract (t - s) = t + ((-⌊t - s⌋ : ℤ) : ℝ) := by
      rw [Int.fract]; push_cast; ring
    rw [this, ploop_int h, hst]
  have h2 := h.inj _ _ h1 (by
    rw [abs_lt]; constructor <;> linarith [Int.fract_nonneg (t - s), Int.fract_lt_one (t - s)])
  refine ⟨⌊t - s⌋, ?_⟩
  have h3 : Int.fract (t - s) = 0 := by linarith
  rw [Int.fract] at h3
  linarith

theorem solution (C : Set Plane) (hC : IsJordanCurve C) :
    ∃ p1 p2 p3 p4 : Plane, p1 ∈ C ∧ p2 ∈ C ∧ p3 ∈ C ∧ p4 ∈ C ∧ IsRectangle p1 p2 p3 p4 := by
  obtain ⟨g, hg⟩ := ploop_of_jordan C hC
  obtain ⟨s, t, s', t', hE, hne⟩ := LefebvreVariations.moebius_band_half_space_embedding
    (fun st => ((1 / 2 : ℝ) • (g st.1 + g st.2), ‖g st.2 - g st.1‖))
    (by have := hg.cont; fun_prop)
    (fun s t => by simp [add_comm, norm_sub_rev])
    (fun s t => by simp [hg.per])
    (fun s t => norm_nonneg _)
    (fun s t => by
      simp only [norm_eq_zero, sub_eq_zero]
      constructor
      · intro h; exact ploop_eq_int hg s t h.symm
      · rintro ⟨n, rfl⟩; exact ploop_int hg s n)
    (fun s t h => by
      simp only [← two_smul ℝ (g s), ← two_smul ℝ (g t), smul_smul] at h
      have h' : g s = g t := by simpa using h
      exact ploop_eq_int hg s t h')
  simp only [Prod.mk.injEq] at hE
  obtain ⟨hmid, hlen⟩ := hE
  have hsum : g s + g t = g s' + g t' := by
    have := congrArg (fun x => (2 : ℝ) • x) hmid
    simpa [smul_smul] using this
  refine ⟨g s, g s', g t, g t', hg.mem _, hg.mem _, hg.mem _, hg.mem _, hsum, ?_, ?_, ?_⟩
  · rw [dist_eq_norm, dist_eq_norm, norm_sub_rev, hlen, norm_sub_rev]
  · intro heq
    have h2 : g t = g t' := by
      have := hsum; rw [heq] at this; exact add_left_cancel this
    obtain ⟨m, hm⟩ := ploop_eq_int hg _ _ heq
    obtain ⟨n, hn⟩ := ploop_eq_int hg _ _ h2
    exact hne (Or.inl ⟨m, n, hm, hn⟩)
  · intro heq
    have h2 : g t' = g s := by
      have h3 : g s' + g t' = g s' + g s := by
        rw [← hsum, ← heq, add_comm]
      exact add_left_cancel h3
    obtain ⟨m, hm⟩ := ploop_eq_int hg _ _ heq.symm
    obtain ⟨n, hn⟩ := ploop_eq_int hg _ _ h2.symm
    exact hne (Or.inr ⟨m, n, hm, hn⟩)
