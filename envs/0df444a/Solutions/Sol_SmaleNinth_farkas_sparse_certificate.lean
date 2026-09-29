-- Prove2me | solution 1 for SmaleNinth.farkas_sparse_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-08T02:30:12.565702+00:00
-- url     : https://prove2.me/submissions/bbf5b0df-e32e-40b1-b673-6dde089ab3a2

import Definitions.Def_Polyhedron
import Theorems.Thm_SmaleNinth_lp_feasible_iff_subsystems
import Mathlib.Tactic

/-!
# Farkas certificates of support at most `n+1`

Helly's theorem, imported as the platform theorem
`SmaleNinth.lp_feasible_iff_subsystems`, produces an infeasible subsystem of at
most `n+1` rows; Farkas' lemma, proved here by Fourier–Motzkin elimination,
produces multipliers for it, which extend by zero to the whole system.

To keep every sum over the same index type, Farkas is applied not to the
subsystem itself but to the full system with the rows outside `S` replaced by
the vacuous inequality `0 ≥ 0`; that system is feasible exactly when the
subsystem is.
-/

open Matrix LinearOptimization Finset

open Matrix LinearOptimization Finset

namespace FarkasDev

/-- Feasibility of the system indexed by an arbitrary finite type. -/
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

end FarkasDev

namespace FarkasDev

open Classical in
/-- The reduced data after eliminating the last variable: rows with vanishing
last coefficient are kept, pairs of rows with opposite last coefficients are
combined. -/
noncomputable def redF {ι : Type} {n : ℕ} (A : ι → Fin (n + 1) → ℝ) (f : ι → ℝ) :
    (ι ⊕ ι × ι) → ℝ
  | Sum.inl i => if A i (Fin.last n) = 0 then f i else 0
  | Sum.inr (i, j) =>
      if 0 < A i (Fin.last n) ∧ A j (Fin.last n) < 0 then
        A i (Fin.last n) * f j - A j (Fin.last n) * f i
      else 0

open Classical in
/-- The multipliers of the original rows obtained from multipliers of the reduced rows. -/
noncomputable def yOf {ι : Type} [Fintype ι] {n : ℕ} (A : ι → Fin (n + 1) → ℝ)
    (z : (ι ⊕ ι × ι) → ℝ) : ι → ℝ := fun i =>
  (if A i (Fin.last n) = 0 then z (Sum.inl i) else 0)
  + (∑ j, if 0 < A i (Fin.last n) ∧ A j (Fin.last n) < 0 then
        (- A j (Fin.last n)) * z (Sum.inr (i, j)) else 0)
  + (∑ j, if 0 < A j (Fin.last n) ∧ A i (Fin.last n) < 0 then
        A j (Fin.last n) * z (Sum.inr (j, i)) else 0)

/-- Transfer of a linear functional along the elimination. -/
lemma transfer {ι : Type} [Fintype ι] {n : ℕ} (A : ι → Fin (n + 1) → ℝ)
    (z : (ι ⊕ ι × ι) → ℝ) (f : ι → ℝ) :
    ∑ i, yOf A z i * f i = ∑ i', z i' * redF A f i' := by
  classical
  rw [Fintype.sum_sum_type]
  have hL : ∑ i, yOf A z i * f i
      = (∑ i, (if A i (Fin.last n) = 0 then z (Sum.inl i) else 0) * f i)
        + (∑ i, ∑ j, (if 0 < A i (Fin.last n) ∧ A j (Fin.last n) < 0 then
            (- A j (Fin.last n)) * z (Sum.inr (i, j)) else 0) * f i)
        + (∑ i, ∑ j, (if 0 < A j (Fin.last n) ∧ A i (Fin.last n) < 0 then
            A j (Fin.last n) * z (Sum.inr (j, i)) else 0) * f i) := by
    simp only [yOf, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  rw [hL]
  have h1 : (∑ i, (if A i (Fin.last n) = 0 then z (Sum.inl i) else 0) * f i)
      = ∑ i, z (Sum.inl i) * redF A f (Sum.inl i) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [redF]
    split_ifs <;> ring
  have h3 : (∑ i, ∑ j, (if 0 < A j (Fin.last n) ∧ A i (Fin.last n) < 0 then
        A j (Fin.last n) * z (Sum.inr (j, i)) else 0) * f i)
      = ∑ i, ∑ j, (if 0 < A i (Fin.last n) ∧ A j (Fin.last n) < 0 then
        A i (Fin.last n) * z (Sum.inr (i, j)) else 0) * f j := by
    rw [Finset.sum_comm]
  rw [Fintype.sum_prod_type, h1, h3, add_assoc]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [redF]
  split_ifs <;> ring

end FarkasDev

namespace FarkasDev

/-- Feasibility is preserved by the elimination. -/
lemma feas_red {ι : Type} [Fintype ι] {n : ℕ} (A : ι → Fin (n + 1) → ℝ) (c : ι → ℝ) :
    Feas A c ↔ Feas (fun i' k => redF A (fun i => A i k.castSucc) i') (redF A c) := by
  classical
  rw [fm_step]
  constructor
  · rintro ⟨y, hZ, hPN⟩
    refine ⟨y, ?_⟩
    rintro (i | ⟨i, j⟩)
    · by_cases h : A i (Fin.last n) = 0
      · have e : ∀ k : Fin n, redF A (fun i => A i k.castSucc) (Sum.inl i) = A i k.castSucc := by
          intro k; simp only [redF, if_pos h]
        simp only [e, redF, if_pos h]
        exact hZ i h
      · simp only [redF, if_neg h]
        simp
    · by_cases h : 0 < A i (Fin.last n) ∧ A j (Fin.last n) < 0
      · have e : ∀ k : Fin n, redF A (fun i => A i k.castSucc) (Sum.inr (i, j))
            = A i (Fin.last n) * A j k.castSucc - A j (Fin.last n) * A i k.castSucc := by
          intro k; simp only [redF, if_pos h]
        simp only [e, redF, if_pos h]
        exact hPN i j h.1 h.2
      · simp only [redF, if_neg h]
        simp
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_, ?_⟩
    · intro i hi
      have := hy (Sum.inl i)
      simp only [redF, if_pos hi] at this
      exact this
    · intro i j hi hj
      have := hy (Sum.inr (i, j))
      simp only [redF, if_pos (And.intro hi hj)] at this
      exact this

/-- The eliminated column receives multiplier zero. -/
lemma redF_last {ι : Type} {n : ℕ} (A : ι → Fin (n + 1) → ℝ) :
    ∀ i', redF A (fun i => A i (Fin.last n)) i' = 0 := by
  classical
  rintro (i | ⟨i, j⟩)
  · simp only [redF]
    split_ifs with h
    · exact h
    · rfl
  · simp only [redF]
    split_ifs with h
    · ring
    · rfl

/-- **Farkas' lemma, certificate form.** An infeasible system of linear inequalities
carries a nonnegative combination of its rows that is identically zero with positive
right-hand side. -/
theorem farkas_cert : ∀ (n : ℕ) {ι : Type} [Fintype ι] (A : ι → Fin n → ℝ) (c : ι → ℝ),
    ¬ Feas A c →
      ∃ y : ι → ℝ, (∀ i, 0 ≤ y i) ∧ (∀ k, ∑ i, y i * A i k = 0) ∧ 0 < ∑ i, y i * c i := by
  intro n
  induction n with
  | zero =>
    intro ι _ A c hinf
    classical
    have hx : ¬ ∀ i, c i ≤ 0 := by
      intro h
      exact hinf ⟨fun _ => 0, fun i => by simpa using h i⟩
    push_neg at hx
    obtain ⟨i₀, hi₀⟩ := hx
    refine ⟨fun i => if i = i₀ then 1 else 0, fun i => by dsimp only; split_ifs <;> norm_num,
      fun k => Fin.elim0 k, ?_⟩
    simpa using hi₀
  | succ n ih =>
    intro ι _ A c hinf
    classical
    have hred : ¬ Feas (fun i' k => redF A (fun i => A i k.castSucc) i') (redF A c) := by
      rw [← feas_red]; exact hinf
    obtain ⟨z, hz0, hzA, hzc⟩ := ih _ _ hred
    refine ⟨yOf A z, ?_, ?_, ?_⟩
    · intro i
      unfold yOf
      have t1 : 0 ≤ (if A i (Fin.last n) = 0 then z (Sum.inl i) else 0) := by
        split_ifs
        · exact hz0 _
        · exact le_rfl
      have t2 : 0 ≤ ∑ j, (if 0 < A i (Fin.last n) ∧ A j (Fin.last n) < 0 then
            (- A j (Fin.last n)) * z (Sum.inr (i, j)) else 0) := by
        refine Finset.sum_nonneg (fun j _ => ?_)
        split_ifs with h
        · exact mul_nonneg (by linarith [h.2]) (hz0 _)
        · exact le_rfl
      have t3 : 0 ≤ ∑ j, (if 0 < A j (Fin.last n) ∧ A i (Fin.last n) < 0 then
            A j (Fin.last n) * z (Sum.inr (j, i)) else 0) := by
        refine Finset.sum_nonneg (fun j _ => ?_)
        split_ifs with h
        · exact mul_nonneg (le_of_lt h.1) (hz0 _)
        · exact le_rfl
      linarith
    · intro k
      rcases Fin.eq_castSucc_or_eq_last k with ⟨k', rfl⟩ | rfl
      · rw [transfer]
        exact hzA k'
      · rw [transfer]
        simp [redF_last A]
    · rw [transfer]
      exact hzc

end FarkasDev


open FarkasDev in
/-- **Sparse Farkas certificate.** -/
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hinf : ¬ (polyhedron A b).Nonempty) :
    ∃ y : Fin m → ℝ, (∀ i, 0 ≤ y i) ∧ (∀ k, ∑ i, y i * A i k = 0) ∧ 0 < ∑ i, y i * b i ∧
      (Finset.univ.filter (fun i => y i ≠ 0)).card ≤ n + 1 := by
  classical
  -- Helly: some subsystem of at most `n+1` rows is already infeasible
  rw [SmaleNinth.lp_feasible_iff_subsystems] at hinf
  push_neg at hinf
  obtain ⟨S, hScard, hS⟩ := hinf
  -- the same system with the rows outside `S` replaced by `0 ≥ 0`
  set A' : Fin m → Fin n → ℝ := fun i k => if i ∈ S then A i k else 0 with hA'
  set b' : Fin m → ℝ := fun i => if i ∈ S then b i else 0 with hb'
  have hinf' : ¬ Feas A' b' := by
    rintro ⟨x, hx⟩
    obtain ⟨i, hiS, hi⟩ := hS x
    have h := hx i
    simp only [hA', hb', if_pos hiS] at h
    simp only [Matrix.mulVec, dotProduct] at hi
    linarith
  obtain ⟨y, hy0, hyA, hyb⟩ := farkas_cert n A' b' hinf'
  refine ⟨fun i => if i ∈ S then y i else 0, ?_, ?_, ?_, ?_⟩
  · intro i; dsimp only; split_ifs with h
    · exact hy0 _
    · exact le_rfl
  · intro k
    have key : ∑ i, (if i ∈ S then y i else 0) * A i k = ∑ i, y i * A' i k :=
      Finset.sum_congr rfl (fun i _ => by simp only [hA']; split_ifs <;> ring)
    rw [key]
    exact hyA k
  · have key : ∑ i, (if i ∈ S then y i else 0) * b i = ∑ i, y i * b' i :=
      Finset.sum_congr rfl (fun i _ => by simp only [hb']; split_ifs <;> ring)
    rw [key]
    exact hyb
  · refine le_trans (Finset.card_le_card ?_) hScard
    intro i hi
    simp only [Finset.mem_filter] at hi
    by_contra hnot
    exact hi.2 (if_neg hnot)
