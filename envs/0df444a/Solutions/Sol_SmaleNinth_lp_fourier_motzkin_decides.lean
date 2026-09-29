-- Prove2me | solution 1 for SmaleNinth.lp_fourier_motzkin_decides
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-08T02:43:44.067076+00:00
-- url     : https://prove2.me/submissions/268d1305-445c-401a-9dec-bcb6bea285b2

import Definitions.Def_Polyhedron
import Definitions.Def_SmaleNinth_FourierMotzkin
import Mathlib.Tactic

/-!
# Fourier–Motzkin elimination decides feasibility

`fm_step` is one elimination, proved for an arbitrary finite index type: a
solution of the reduced system extends to the original one by choosing the last
coordinate between the largest lower bound and the smallest upper bound, and
conversely every reduced inequality is a nonnegative combination of two
original ones.  `feas_elim` recognises the reduced system of
`Def_SmaleNinth_FourierMotzkin` as the one appearing there — the rows and pairs
of the wrong kind carry the vacuous inequality `0 ≥ 0` — and induction on the
number of variables gives the theorem.
-/

open Matrix LinearOptimization Finset SmaleNinth

namespace FMDecides

/-- Feasibility of a system indexed by an arbitrary finite type. -/
def Feas {ι : Type} [Fintype ι] {n : ℕ} (A : ι → Fin n → ℝ) (c : ι → ℝ) : Prop :=
  ∃ x : Fin n → ℝ, ∀ i, c i ≤ ∑ k, A i k * x k



/-- Fourier–Motzkin elimination of the last variable, for an arbitrary finite index type. -/
theorem fm_step {ι : Type} [Fintype ι] {n : ℕ} (A : ι → Fin (n + 1) → ℝ) (c : ι → ℝ) :
    Feas A c ↔
      ∃ y : Fin n → ℝ,
        (∀ i, A i (Fin.last n) = 0 → c i ≤ ∑ k : Fin n, A i k.castSucc * y k) ∧
        (∀ i j, 0 < A i (Fin.last n) → A j (Fin.last n) < 0 →
            A i (Fin.last n) * c j - A j (Fin.last n) * c i ≤
              ∑ k : Fin n, (A i (Fin.last n) * A j k.castSucc
                - A j (Fin.last n) * A i k.castSucc) * y k) := by
  classical
  have hmv : ∀ (x : Fin (n + 1) → ℝ) (i : ι),
      (∑ k, A i k * x k)
        = (∑ k : Fin n, A i k.castSucc * x k.castSucc) + A i (Fin.last n) * x (Fin.last n) :=
    fun x i => Fin.sum_univ_castSucc _
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
    set S : ι → ℝ := fun i => ∑ k : Fin n, A i k.castSucc * y k with hS
    set B : ι → ℝ := fun i => A i (Fin.last n) with hB
    have hpair : ∀ i j, 0 < B i → B j < 0 → B i * c j - B j * c i ≤ B i * S j - B j * S i := by
      intro i j hi hj
      have h := hPN i j hi hj
      have hsum : ∑ k : Fin n, (A i (Fin.last n) * A j k.castSucc
            - A j (Fin.last n) * A i k.castSucc) * y k = B i * S j - B j * S i := by
        rw [hS, hB]
        simp only
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun k _ => by ring)
      rw [hsum] at h
      exact h
    set P : Finset ι := Finset.univ.filter (fun i => 0 < B i) with hPdef
    set N : Finset ι := Finset.univ.filter (fun i => B i < 0) with hNdef
    have key : ∀ v : ℝ,
        (∀ i ∈ P, (c i - S i) / B i ≤ v) → (∀ j ∈ N, v ≤ (c j - S j) / B j) → Feas A c := by
      intro v hlow hup
      refine ⟨Fin.snoc y v, fun i => ?_⟩
      have hval : (∑ k, A i k * (Fin.snoc y v : Fin (n+1) → ℝ) k) = S i + B i * v := by
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


/-- One elimination step in the form of `Def_SmaleNinth_FourierMotzkin`. -/
lemma feas_elim {ι : Type} [Fintype ι] {n : ℕ} (A : ι → Fin (n + 1) → ℝ) (c : ι → ℝ) :
    Feas A c ↔ Feas (elimMatrix A) (elimStep A c) := by
  classical
  rw [fm_step]
  constructor
  · rintro ⟨y, hZ, hPN⟩
    refine ⟨y, ?_⟩
    rintro (i | ⟨i, j⟩)
    · by_cases h : A i (Fin.last n) = 0
      · have e : ∀ k : Fin n, elimMatrix A (Sum.inl i) k = A i k.castSucc := by
          intro k; simp only [elimMatrix, elimStep, if_pos h]
        simp only [e, elimStep, if_pos h]
        exact hZ i h
      · simp only [elimMatrix, elimStep, if_neg h]
        simp
    · by_cases h : 0 < A i (Fin.last n) ∧ A j (Fin.last n) < 0
      · have e : ∀ k : Fin n, elimMatrix A (Sum.inr (i, j)) k
            = A i (Fin.last n) * A j k.castSucc - A j (Fin.last n) * A i k.castSucc := by
          intro k; simp only [elimMatrix, elimStep, if_pos h]
        simp only [e, elimStep, if_pos h]
        exact hPN i j h.1 h.2
      · simp only [elimMatrix, elimStep, if_neg h]
        simp
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_, ?_⟩
    · intro i hi
      have h := hy (Sum.inl i)
      simp only [elimMatrix, elimStep, if_pos hi] at h
      exact h
    · intro i j hi hj
      have h := hy (Sum.inr (i, j))
      simp only [elimMatrix, elimStep, if_pos (And.intro hi hj)] at h
      exact h

/-- Correctness of the whole procedure. -/
theorem feas_iff_elimFeas : ∀ (n : ℕ) {ι : Type} [Fintype ι] (A : ι → Fin n → ℝ) (c : ι → ℝ),
    Feas A c ↔ ElimFeas n A c := by
  intro n
  induction n with
  | zero =>
    intro ι _ A c
    constructor
    · rintro ⟨x, hx⟩ i
      simpa using hx i
    · intro h
      exact ⟨fun _ => 0, fun i => by simpa using h i⟩
  | succ n ih =>
    intro ι _ A c
    rw [feas_elim A c]
    exact ih _ _

end FMDecides

open FMDecides in
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    (polyhedron A b).Nonempty ↔ ElimFeas n (fun i k => A i k) b := by
  rw [← feas_iff_elimFeas]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, fun i => by simpa [Matrix.mulVec, dotProduct] using hx i⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, fun i => by simpa [Matrix.mulVec, dotProduct] using hx i⟩
