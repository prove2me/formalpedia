-- Prove2me | solution 1 for PoissonDepTrials.MixInv.theorem_4_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T15:54:41.971751+00:00
-- url     : https://prove2.me/submissions/0ba793c5-30e0-4b85-9303-08d063c612dd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_PoissonDepTrials_MixInv_Setting
import Theorems.Thm_PoissonDepTrials_MixInv_bound_4_14
import Theorems.Thm_PoissonDepTrials_MixInv_bound_4_18
import Theorems.Thm_PoissonDepTrials_MixInv_bound_4_19
import Theorems.Thm_PoissonDepTrials_MixInv_lemma_4_5
import Theorems.Thm_PoissonDepTrials_MixInv_cauchy_schwarz_4_10

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace PoissonDepTrials.MixInv

theorem card_A_5f2cbe01 (n m i : ℕ) :
    ((Finset.Icc 1 n).filter (fun j : ℕ =>
      0 < |(i : ℤ) - ((j : ℕ) : ℤ)| ∧ |(i : ℤ) - ((j : ℕ) : ℤ)| ≤ m)).card ≤ 2 * m := by
  have h := Finset.card_le_card_of_injOn (fun j : ℕ => (j : ℤ))
    (s := (Finset.Icc 1 n).filter (fun j : ℕ =>
      0 < |(i : ℤ) - ((j : ℕ) : ℤ)| ∧ |(i : ℤ) - ((j : ℕ) : ℤ)| ≤ m))
    (t := (Finset.Icc ((i : ℤ) - m) ((i : ℤ) + m)).erase (i : ℤ)) ?_ ?_
  · rw [Finset.card_erase_of_mem (by simp), Int.card_Icc] at h
    omega
  · intro j hj
    simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at hj
    simp only [Finset.coe_erase, Finset.coe_Icc, Set.mem_sdiff, Set.mem_Icc,
      Set.mem_singleton_iff]
    have h1 := abs_le.mp hj.2.2
    have h2 : (i : ℤ) - (j : ℤ) ≠ 0 := abs_pos.mp hj.2.1
    refine ⟨⟨by linarith [h1.1, h1.2], by linarith [h1.1, h1.2]⟩, ?_⟩
    intro hji
    exact h2 (by rw [hji]; ring)
  · intro a _ b _ hab
    simpa using hab

theorem card_B_5f2cbe01 (n m i : ℕ) :
    ((Finset.Icc 1 n).filter (fun j : ℕ => |(i : ℤ) - ((j : ℕ) : ℤ)| ≤ m)).card ≤ 2 * m + 1 := by
  have h := Finset.card_le_card_of_injOn (fun j : ℕ => (j : ℤ))
    (s := (Finset.Icc 1 n).filter (fun j : ℕ => |(i : ℤ) - ((j : ℕ) : ℤ)| ≤ m))
    (t := Finset.Icc ((i : ℤ) - m) ((i : ℤ) + m)) ?_ ?_
  · rw [Int.card_Icc] at h
    omega
  · intro j hj
    simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at hj
    simp only [Finset.coe_Icc, Set.mem_Icc]
    have := abs_le.mp hj.2
    constructor <;> linarith [this.1, this.2]
  · intro a _ b _ hab
    simpa using hab

theorem sum_row_5f2cbe01 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (n : ℕ)
    (X : ℕ → Ω → ℕ) (a : ℝ) :
    ∑ i ∈ Finset.Icc 1 n, a * (n * prob P X i + lam P n X)
      = a * (n * lam P n X + n * lam P n X) := by
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Nat.card_Icc, nsmul_eq_mul]
  simp [lam]

theorem lam_zero_case_5f2cbe01 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X)
    (h : ℕ → ℝ) (hl : lam P n X = 0) :
    ∫ ω, h (W n X ω) ∂P - poissonExp (lam P n X) h = 0 := by
  have hp : ∀ i ∈ Finset.Icc 1 n, prob P X i = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => measureReal_nonneg)).mp hl
  have hae : ∀ i ∈ Finset.Icc 1 n, ∀ᵐ ω ∂P, X i ω = 0 := by
    intro i hi
    have h0 : P {ω | X i ω = 1} = 0 := by
      have := hp i hi
      unfold prob at this
      exact (measureReal_eq_zero_iff).mp this
    have h1 : ∀ᵐ ω ∂P, ¬ (X i ω = 1) := by
      rw [ae_iff]; simpa using h0
    filter_upwards [h1, hX.2.2 i] with ω hω1 hω2
    omega
  have hW : ∀ᵐ ω ∂P, W n X ω = 0 := by
    have := (Filter.eventually_all_finset (Finset.Icc 1 n)).mpr hae
    filter_upwards [this] with ω hω
    unfold W
    exact Finset.sum_eq_zero hω
  have hint : ∫ ω, h (W n X ω) ∂P = h 0 := by
    rw [integral_congr_ae (g := fun _ => h 0) (by filter_upwards [hW] with ω hω; rw [hω])]
    simp
  have hpe : poissonExp (lam P n X) h = h 0 := by
    rw [hl]; unfold poissonExp
    rw [tsum_eq_single 0 (fun k hk => by simp [zero_pow hk])]
    simp
  rw [hint, hpe]; ring

end PoissonDepTrials.MixInv

open PoissonDepTrials.MixInv in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (φ : ℕ → ℝ) (hφ : IbragimovMixing P X φ) (m : ℕ)
    (h : ℕ → ℝ) (hh : ∀ k, |h k| ≤ 1) :
    |∫ ω, h (W n X ω) ∂P - poissonExp (lam P n X) h| ≤
      2 * (lam P n X)⁻¹ * (8 * m + 5 + 4 * Real.sqrt ((n : ℝ) * φ (m + 1)))
          * (Var[fun ω => (W n X ω : ℝ); P] - lam P n X
              + 2 * (2 * m + 1) * ∑ i ∈ Finset.Icc 1 n, prob P X i ^ 2)
        + 32 * (6 * m + 3 + Real.sqrt ((n : ℝ) * φ (m + 1))) * n * φ (m + 1) := by
  have hφ0 : 0 ≤ φ (m + 1) := hφ.1.le_of_tendsto hφ.2.1 (m + 1)
  have hs0 : 0 ≤ Real.sqrt ((n : ℝ) * φ (m + 1)) := Real.sqrt_nonneg _
  have hl0 : 0 ≤ lam P n X := Finset.sum_nonneg (fun i _ => measureReal_nonneg)
  rcases hl0.eq_or_lt with hl | hl
  · rw [lam_zero_case_5f2cbe01 P n X hX h hl.symm, ← hl]
    simp only [abs_zero, inv_zero, mul_zero, zero_mul, zero_add]
    exact mul_nonneg (mul_nonneg (by positivity) (Nat.cast_nonneg n)) hφ0
  have hl' : lam P n X ≠ 0 := hl.ne'
  have h14 := bound_4_14 P n X hX hl φ hφ m h hh
  have h45 := lemma_4_5 P n X hX φ hφ m
  have hcs := cauchy_schwarz_4_10 P n X m
  obtain ⟨c, hc⟩ : ∃ c, min (1 / Real.sqrt (lam P n X)) 1 = c := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, (8 * m + 5 + 4 * Real.sqrt ((n : ℝ) * φ (m + 1)) : ℝ) = K := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := hc ▸ le_min (by positivity) zero_le_one
  have hc1 : c ≤ 1 := hc ▸ min_le_right _ _
  have hK0 : 0 ≤ K := hK ▸ by positivity
  have hp0 : ∀ i, 0 ≤ prob P X i := fun i => measureReal_nonneg
  rw [hc] at h14
  rw [hK]
  -- first double sum
  have hS1 : ∑ i ∈ Finset.Icc 1 n,
          ∑ j ∈ Finset.Icc 1 n with 0 < |(i : ℤ) - ((j : ℕ) : ℤ)| ∧ |(i : ℤ) - ((j : ℕ) : ℤ)| ≤ m,
            ∫ ω, (X i ω : ℝ) * X j ω *
              (1 + 2 * c * |(Y' n m X i ((j : ℤ) - 1) ω : ℝ) + 1 - lam P n X|) ∂P
        ≤ (∑ i ∈ Finset.Icc 1 n,
          ∑ j ∈ Finset.Icc 1 n with 0 < |(i : ℤ) - ((j : ℕ) : ℤ)| ∧ |(i : ℤ) - ((j : ℕ) : ℤ)| ≤ m,
            ∫ ω, (X i ω : ℝ) * X j ω ∂P) * K
          + 2 * m * (8 * c * φ (m + 1)) * (n * lam P n X + n * lam P n X) := by
    rw [Finset.sum_mul, ← sum_row_5f2cbe01, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i hi
    calc _ ≤ ∑ j ∈ Finset.Icc 1 n with 0 < |(i : ℤ) - ((j : ℕ) : ℤ)| ∧ |(i : ℤ) - ((j : ℕ) : ℤ)| ≤ m,
            ((∫ ω, (X i ω : ℝ) * X j ω ∂P) * K
              + 8 * c * (n * prob P X i + lam P n X) * φ (m + 1)) := by
          apply Finset.sum_le_sum
          intro j hj
          obtain ⟨hj1, hj2⟩ := Finset.mem_filter.mp hj
          have := bound_4_18 P n X hX φ hφ m i j hi hj1 hj2
          rw [hc, hK] at this
          exact this
      _ = (∑ j ∈ Finset.Icc 1 n with 0 < |(i : ℤ) - ((j : ℕ) : ℤ)| ∧ |(i : ℤ) - ((j : ℕ) : ℤ)| ≤ m,
            ∫ ω, (X i ω : ℝ) * X j ω ∂P) * K
            + ((Finset.Icc 1 n).filter (fun j : ℕ =>
              0 < |(i : ℤ) - ((j : ℕ) : ℤ)| ∧ |(i : ℤ) - ((j : ℕ) : ℤ)| ≤ m)).card
              * (8 * c * (n * prob P X i + lam P n X) * φ (m + 1)) := by
          rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := by
          have hcard : ((((Finset.Icc 1 n).filter (fun j : ℕ =>
              0 < |(i : ℤ) - ((j : ℕ) : ℤ)| ∧ |(i : ℤ) - ((j : ℕ) : ℤ)| ≤ m)).card : ℕ) : ℝ)
              ≤ 2 * m := by exact_mod_cast card_A_5f2cbe01 n m i
          have ht : 0 ≤ 8 * c * (n * prob P X i + lam P n X) * φ (m + 1) := by
            have := hp0 i; positivity
          nlinarith
  -- second double sum
  have hS2 : ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with |(i : ℤ) - ((j : ℕ) : ℤ)| ≤ m,
            prob P X i * ∫ ω, (X j ω : ℝ) *
              (1 + 2 * c * |(Y n m X i ((j : ℤ) - 1) ω : ℝ) + 1 - lam P n X|) ∂P
        ≤ (∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with |(i : ℤ) - ((j : ℕ) : ℤ)| ≤ m,
            prob P X i * prob P X j) * K
          + (2 * m + 1) * (8 * c * φ (m + 1)) * (n * lam P n X + n * lam P n X) := by
    rw [Finset.sum_mul, ← sum_row_5f2cbe01, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i hi
    calc _ ≤ ∑ j ∈ Finset.Icc 1 n with |(i : ℤ) - ((j : ℕ) : ℤ)| ≤ m,
            (prob P X i * prob P X j * K
              + 8 * c * (n * prob P X i + lam P n X) * φ (m + 1)) := by
          apply Finset.sum_le_sum
          intro j hj
          obtain ⟨hj1, hj2⟩ := Finset.mem_filter.mp hj
          have := bound_4_19 P n X hX φ hφ m i j hi hj1 hj2
          rw [hc, hK] at this
          exact this
      _ = (∑ j ∈ Finset.Icc 1 n with |(i : ℤ) - ((j : ℕ) : ℤ)| ≤ m,
            prob P X i * prob P X j) * K
            + ((Finset.Icc 1 n).filter (fun j : ℕ => |(i : ℤ) - ((j : ℕ) : ℤ)| ≤ m)).card
              * (8 * c * (n * prob P X i + lam P n X) * φ (m + 1)) := by
          rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := by
          have hcard : ((((Finset.Icc 1 n).filter (fun j : ℕ =>
              |(i : ℤ) - ((j : ℕ) : ℤ)| ≤ m)).card : ℕ) : ℝ)
              ≤ 2 * m + 1 := by exact_mod_cast card_B_5f2cbe01 n m i
          have ht : 0 ≤ 8 * c * (n * prob P X i + lam P n X) * φ (m + 1) := by
            have := hp0 i; positivity
          nlinarith
  -- name the atoms
  generalize hE : (∑ i ∈ Finset.Icc 1 n,
          ∑ j ∈ Finset.Icc 1 n with 0 < |(i : ℤ) - ((j : ℕ) : ℤ)| ∧ |(i : ℤ) - ((j : ℕ) : ℤ)| ≤ m,
            ∫ ω, (X i ω : ℝ) * X j ω ∂P) = E at hS1 h45
  generalize hQ : (∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with |(i : ℤ) - ((j : ℕ) : ℤ)| ≤ m,
            prob P X i * prob P X j) = Q at hS2 hcs
  generalize hS1' : (∑ i ∈ Finset.Icc 1 n,
          ∑ j ∈ Finset.Icc 1 n with 0 < |(i : ℤ) - ((j : ℕ) : ℤ)| ∧ |(i : ℤ) - ((j : ℕ) : ℤ)| ≤ m,
            ∫ ω, (X i ω : ℝ) * X j ω *
              (1 + 2 * c * |(Y' n m X i ((j : ℤ) - 1) ω : ℝ) + 1 - lam P n X|) ∂P) = S1 at hS1 h14
  generalize hS2' : (∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with |(i : ℤ) - ((j : ℕ) : ℤ)| ≤ m,
            prob P X i * ∫ ω, (X j ω : ℝ) *
              (1 + 2 * c * |(Y n m X i ((j : ℤ) - 1) ω : ℝ) + 1 - lam P n X|) ∂P) = S2 at hS2 h14
  have ha : 0 ≤ 2 * (lam P n X)⁻¹ := by positivity
  have e1 : 2 * (lam P n X)⁻¹ * S1 ≤ 2 * (lam P n X)⁻¹ * ((Var[fun ω => (W n X ω : ℝ); P] - lam P n X
      + (2 * m + 1) * ∑ i ∈ Finset.Icc 1 n, prob P X i ^ 2 + 4 * lam P n X * n * φ (m + 1)) * K
      + 2 * m * (8 * c * φ (m + 1)) * (n * lam P n X + n * lam P n X)) :=
    mul_le_mul_of_nonneg_left (hS1.trans (by nlinarith)) ha
  have e2 : 2 * (lam P n X)⁻¹ * S2 ≤ 2 * (lam P n X)⁻¹ * ((2 * m + 1)
      * (∑ i ∈ Finset.Icc 1 n, prob P X i ^ 2) * K
      + (2 * m + 1) * (8 * c * φ (m + 1)) * (n * lam P n X + n * lam P n X)) :=
    mul_le_mul_of_nonneg_left (hS2.trans (by nlinarith)) ha
  generalize hV : Var[fun ω => (W n X ω : ℝ); P] = V at e1 ⊢
  generalize hsq : ∑ i ∈ Finset.Icc 1 n, prob P X i ^ 2 = R at e1 e2 ⊢
  generalize hs : Real.sqrt ((n : ℝ) * φ (m + 1)) = s at hK hs0 ⊢
  generalize hlam : lam P n X = l at hl' e1 e2 h14 ⊢
  generalize hφv : φ (m + 1) = f at hφ0 hK e1 e2 h14 ⊢
  have heq : 2 * l⁻¹ * ((V - l + (2 * m + 1) * R + 4 * l * n * f) * K
      + 2 * m * (8 * c * f) * (n * l + n * l))
      + 2 * l⁻¹ * ((2 * m + 1) * R * K + (2 * m + 1) * (8 * c * f) * (n * l + n * l))
      = 2 * l⁻¹ * K * (V - l + 2 * (2 * m + 1) * R)
        + 8 * K * n * f + c * (n * f) * (64 * m + 32 * (2 * m + 1)) := by
    field_simp
    ring
  have hnf : 0 ≤ (n : ℝ) * f := by positivity
  have h1 : c * ((n * f) * (64 * m + 32 * (2 * m + 1) + 24))
      ≤ 1 * ((n * f) * (64 * m + 32 * (2 * m + 1) + 24)) :=
    mul_le_mul_of_nonneg_right hc1 (by positivity)
  have hKnf : 8 * K * n * f = (n * f) * (64 * m + 40 + 32 * s) := by rw [← hK]; ring
  have e3 : c * (n * f) * (64 * m + 32 * (2 * m + 1)) + 24 * c * n * f
      = c * ((n * f) * (64 * m + 32 * (2 * m + 1) + 24)) := by ring
  have e4 : 32 * (6 * m + 3 + s) * n * f
      = (n * f) * (64 * m + 40 + 32 * s) + 1 * ((n * f) * (64 * m + 32 * (2 * m + 1) + 24)) := by
    ring
  linarith
