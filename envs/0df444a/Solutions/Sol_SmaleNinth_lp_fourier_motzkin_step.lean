-- Prove2me | solution 1 for SmaleNinth.lp_fourier_motzkin_step
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-08T01:47:42.817441+00:00
-- url     : https://prove2.me/submissions/25b1a99d-ee95-462f-bb49-27213450c36d

import Definitions.Def_Polyhedron
import Mathlib.Tactic

open Matrix LinearOptimization Finset

/-- **Fourier–Motzkin elimination of one variable, any dimension.** -/
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin (n + 1)) ℝ) (c : Fin m → ℝ) :
    (polyhedron A c).Nonempty ↔
      ∃ y : Fin n → ℝ,
        (∀ i : Fin m, A i (Fin.last n) = 0 →
            c i ≤ ∑ k : Fin n, A i k.castSucc * y k) ∧
        (∀ i j : Fin m, 0 < A i (Fin.last n) → A j (Fin.last n) < 0 →
            A i (Fin.last n) * c j - A j (Fin.last n) * c i ≤
              ∑ k : Fin n, (A i (Fin.last n) * A j k.castSucc
                - A j (Fin.last n) * A i k.castSucc) * y k) := by
  classical
  -- the value of one row on a vector, split off the last coordinate
  have hmv : ∀ (x : Fin (n + 1) → ℝ) (i : Fin m),
      (A.mulVec x) i
        = (∑ k : Fin n, A i k.castSucc * x k.castSucc) + A i (Fin.last n) * x (Fin.last n) := by
    intro x i
    simp only [Matrix.mulVec, dotProduct]
    exact Fin.sum_univ_castSucc _
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨fun k => x k.castSucc, ?_, ?_⟩
    · intro i hi
      have := hx i
      rw [hmv, hi] at this
      linarith
    · intro i j hi hj
      have h1 := hx i
      have h2 := hx j
      rw [hmv] at h1 h2
      have hsum : ∑ k : Fin n, (A i (Fin.last n) * A j k.castSucc
            - A j (Fin.last n) * A i k.castSucc) * x k.castSucc
          = A i (Fin.last n) * (∑ k : Fin n, A j k.castSucc * x k.castSucc)
            - A j (Fin.last n) * (∑ k : Fin n, A i k.castSucc * x k.castSucc) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun k _ => by ring)
      rw [hsum]
      nlinarith [mul_le_mul_of_nonneg_left h1 (le_of_lt (neg_pos.mpr hj)),
        mul_le_mul_of_nonneg_left h2 (le_of_lt hi)]
  · rintro ⟨y, hZ, hPN⟩
    set S : Fin m → ℝ := fun i => ∑ k : Fin n, A i k.castSucc * y k with hS
    set B : Fin m → ℝ := fun i => A i (Fin.last n) with hB
    have hpair : ∀ i j : Fin m, 0 < B i → B j < 0 →
        B i * c j - B j * c i ≤ B i * S j - B j * S i := by
      intro i j hi hj
      have := hPN i j hi hj
      have hsum : ∑ k : Fin n, (A i (Fin.last n) * A j k.castSucc
            - A j (Fin.last n) * A i k.castSucc) * y k
          = B i * S j - B j * S i := by
        rw [hS, hB]
        simp only
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun k _ => by ring)
      rw [hsum] at this
      exact this
    set P : Finset (Fin m) := Finset.univ.filter (fun i => 0 < B i) with hPdef
    set N : Finset (Fin m) := Finset.univ.filter (fun i => B i < 0) with hNdef
    have key : ∀ v : ℝ,
        (∀ i ∈ P, (c i - S i) / B i ≤ v) →
        (∀ j ∈ N, v ≤ (c j - S j) / B j) →
        (polyhedron A c).Nonempty := by
      intro v hlow hup
      refine ⟨Fin.snoc y v, fun i => ?_⟩
      have hval : (A.mulVec (Fin.snoc y v)) i = S i + B i * v := by
        rw [hmv]
        simp [hS, hB, Fin.snoc_castSucc, Fin.snoc_last]
      rw [hval]
      rcases lt_trichotomy (B i) 0 with hneg | hzero | hpos
      · have := hup i (by simp [hNdef, hneg])
        rw [le_div_iff_of_neg hneg] at this
        linarith
      · have h0 : A i (Fin.last n) = 0 := hzero
        have := hZ i h0
        rw [hzero]
        simpa [hS] using this
      · have := hlow i (by simp [hPdef, hpos])
        rw [div_le_iff₀ hpos] at this
        linarith
    by_cases hP : P.Nonempty
    · obtain ⟨i₀, hi₀, hmax⟩ := P.exists_max_image (fun i => (c i - S i) / B i) hP
      refine key ((c i₀ - S i₀) / B i₀) (fun i hi => hmax i hi) (fun j hj => ?_)
      have hi₀' : 0 < B i₀ := by simpa [hPdef] using hi₀
      have hj' : B j < 0 := by simpa [hNdef] using hj
      have hp := hpair i₀ j hi₀' hj'
      rw [le_div_iff_of_neg hj', div_mul_eq_mul_div, le_div_iff₀ hi₀']
      nlinarith [hp]
    · by_cases hN : N.Nonempty
      · obtain ⟨j₀, hj₀, hmin⟩ := N.exists_min_image (fun j => (c j - S j) / B j) hN
        exact key ((c j₀ - S j₀) / B j₀) (fun i hi => absurd ⟨i, hi⟩ hP) (fun j hj => hmin j hj)
      · exact key 0 (fun i hi => absurd ⟨i, hi⟩ hP) (fun j hj => absurd ⟨j, hj⟩ hN)
