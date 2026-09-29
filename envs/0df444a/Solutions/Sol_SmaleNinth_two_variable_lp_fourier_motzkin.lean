-- Prove2me | solution 1 for SmaleNinth.two_variable_lp_fourier_motzkin
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-08T01:43:44.66776+00:00
-- url     : https://prove2.me/submissions/df1aedd0-6eb7-432a-b5cc-c99ae3a39bc9

import Definitions.Def_Polyhedron
import Mathlib.Tactic

open Matrix LinearOptimization Finset

/-- **Fourier–Motzkin elimination in two variables.** -/
theorem solution {m : ℕ} (A : Matrix (Fin m) (Fin 2) ℝ) (c : Fin m → ℝ) :
    (polyhedron A c).Nonempty ↔
      ∃ t : ℝ,
        (∀ i : Fin m, A i 1 = 0 → c i ≤ A i 0 * t) ∧
        (∀ i j : Fin m, 0 < A i 1 → A j 1 < 0 →
          A i 1 * c j - A j 1 * c i ≤ (A i 1 * A j 0 - A j 1 * A i 0) * t) := by
  have hmv : ∀ (x : Fin 2 → ℝ) (i : Fin m), (A.mulVec x) i = A i 0 * x 0 + A i 1 * x 1 := by
    intro x i
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x 0, ?_, ?_⟩
    · intro i hi
      have := hx i
      rw [hmv] at this
      rw [hi] at this
      linarith
    · intro i j hi hj
      have h1 := hx i
      have h2 := hx j
      rw [hmv] at h1 h2
      nlinarith [mul_le_mul_of_nonneg_left h1 (le_of_lt (neg_pos.mpr hj)),
        mul_le_mul_of_nonneg_left h2 (le_of_lt hi)]
  · rintro ⟨t, hZ, hPN⟩
    set P : Finset (Fin m) := Finset.univ.filter (fun i => 0 < A i 1) with hPdef
    set N : Finset (Fin m) := Finset.univ.filter (fun i => A i 1 < 0) with hNdef
    have key : ∀ y : ℝ,
        (∀ i ∈ P, (c i - A i 0 * t) / A i 1 ≤ y) →
        (∀ j ∈ N, y ≤ (c j - A j 0 * t) / A j 1) →
        (polyhedron A c).Nonempty := by
      intro y hlow hup
      refine ⟨![t, y], fun i => ?_⟩
      have hval : (A.mulVec ![t, y]) i = A i 0 * t + A i 1 * y := by
        rw [hmv]; simp
      rw [hval]
      rcases lt_trichotomy (A i 1) 0 with hneg | hzero | hpos
      · have := hup i (by simp [hNdef, hneg])
        rw [le_div_iff_of_neg hneg] at this
        linarith
      · rw [hzero]
        have := hZ i hzero
        linarith
      · have := hlow i (by simp [hPdef, hpos])
        rw [div_le_iff₀ hpos] at this
        linarith
    by_cases hP : P.Nonempty
    · obtain ⟨i₀, hi₀, hmax⟩ :=
        P.exists_max_image (fun i => (c i - A i 0 * t) / A i 1) hP
      refine key ((c i₀ - A i₀ 0 * t) / A i₀ 1) (fun i hi => hmax i hi) (fun j hj => ?_)
      have hi₀' : 0 < A i₀ 1 := by simpa [hPdef] using hi₀
      have hj' : A j 1 < 0 := by simpa [hNdef] using hj
      have hpair := hPN i₀ j hi₀' hj'
      rw [le_div_iff_of_neg hj', div_mul_eq_mul_div, le_div_iff₀ hi₀']
      nlinarith [hpair]
    · by_cases hN : N.Nonempty
      · obtain ⟨j₀, hj₀, hmin⟩ :=
          N.exists_min_image (fun j => (c j - A j 0 * t) / A j 1) hN
        exact key ((c j₀ - A j₀ 0 * t) / A j₀ 1)
          (fun i hi => absurd ⟨i, hi⟩ hP) (fun j hj => hmin j hj)
      · exact key 0 (fun i hi => absurd ⟨i, hi⟩ hP) (fun j hj => absurd ⟨j, hj⟩ hN)
