-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P17.sifting_surplus
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-02T23:52:25.333314+00:00
-- url     : https://prove2.me/submissions/cf5b86c9-e979-4209-9b4a-42ae5ace2e48

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P17

section Mod_FKR_Cheb
/-!
# Chebyshev bound for the number of successes in independent trials
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace FKR

section Cheb

variable {γ : Type} [Fintype γ] {m : ℕ}

lemma sum_prod_mul_prod (μ : γ → ℝ) (h : Fin m → γ → ℝ) :
    ∑ w : Fin m → γ, (∏ t, μ (w t)) * ∏ t, h t (w t) = ∏ t, ∑ x, μ x * h t x := by
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.prod_mul_distrib]

lemma sum_prod_one (μ : γ → ℝ) (hμ1 : ∑ g, μ g = 1) :
    ∑ w : Fin m → γ, ∏ t, μ (w t) = 1 := by
  have := sum_prod_mul_prod (m := m) μ (fun _ _ => 1)
  simp only [Finset.prod_const_one, mul_one] at this
  rw [this, hμ1, Finset.prod_const_one]

variable (μ : γ → ℝ) (ind : γ → ℝ)

lemma sum_prod_ind (hμ1 : ∑ g, μ g = 1) (t0 : Fin m) :
    ∑ w : Fin m → γ, (∏ t, μ (w t)) * ind (w t0) = ∑ x, μ x * ind x := by
  have := sum_prod_mul_prod μ (fun t x => if t = t0 then ind x else 1)
  have e : ∀ w : Fin m → γ, ∏ t, (if t = t0 then ind (w t) else 1) = ind (w t0) := by
    intro w
    rw [Finset.prod_ite_eq']
    simp
  simp only [e] at this
  rw [this]
  have e2 : ∀ t : Fin m, ∑ x, μ x * (if t = t0 then ind x else 1) =
      if t = t0 then ∑ x, μ x * ind x else 1 := by
    intro t
    by_cases ht : t = t0
    · simp [ht]
    · simp [ht, hμ1]
  simp only [e2]
  rw [Finset.prod_ite_eq']
  simp

lemma sum_prod_ind2 (hμ1 : ∑ g, μ g = 1) (hind : ∀ x, ind x * ind x = ind x) (t1 t2 : Fin m) :
    ∑ w : Fin m → γ, (∏ t, μ (w t)) * (ind (w t1) * ind (w t2)) =
      if t1 = t2 then ∑ x, μ x * ind x else (∑ x, μ x * ind x) ^ 2 := by
  have := sum_prod_mul_prod μ (fun t x => (if t = t1 then ind x else 1) * (if t = t2 then ind x else 1))
  have e : ∀ w : Fin m → γ,
      ∏ t, ((if t = t1 then ind (w t) else 1) * (if t = t2 then ind (w t) else 1)) =
        ind (w t1) * ind (w t2) := by
    intro w
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.prod_ite_eq']
    simp
  simp only [e] at this
  rw [this]
  set q := ∑ x, μ x * ind x
  by_cases h12 : t1 = t2
  · subst h12
    rw [if_pos rfl]
    have e2 : ∀ t : Fin m, ∑ x, μ x * ((if t = t1 then ind x else 1) * (if t = t1 then ind x else 1))
        = if t = t1 then q else 1 := by
      intro t
      by_cases ht : t = t1
      · simp only [ht, if_true, hind]; rfl
      · simp [ht, hμ1]
    simp only [e2]
    rw [Finset.prod_ite_eq']
    simp
  · rw [if_neg h12]
    have e2 : ∀ t : Fin m, ∑ x, μ x * ((if t = t1 then ind x else 1) * (if t = t2 then ind x else 1))
        = (if t = t1 then q else 1) * (if t = t2 then q else 1) := by
      intro t
      by_cases ht1 : t = t1 <;> by_cases ht2 : t = t2
      · exact absurd (ht1.symm.trans ht2) h12
      · subst ht1; simp [h12, q]
      · subst ht2; simp [Ne.symm h12, q]
      · simp [ht1, ht2, hμ1]
    simp only [e2]
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.prod_ite_eq']
    simp [sq]

/-- Variance of the number of successes. -/
lemma variance_count (hμ1 : ∑ g, μ g = 1) (hind : ∀ x, ind x * ind x = ind x) :
    ∑ w : Fin m → γ, (∏ t, μ (w t)) * (∑ t, ind (w t) - m * ∑ x, μ x * ind x) ^ 2 =
      m * (∑ x, μ x * ind x) * (1 - ∑ x, μ x * ind x) := by
  obtain ⟨q, hq⟩ : ∃ q, q = ∑ x, μ x * ind x := ⟨_, rfl⟩
  rw [← hq]
  have hS0 : ∑ w : Fin m → γ, ∏ t, μ (w t) = 1 := sum_prod_one μ hμ1
  have hS2 : ∑ w : Fin m → γ, (∏ t, μ (w t)) * ∑ t, ind (w t) = m * q := by
    have e : ∀ w : Fin m → γ, (∏ t, μ (w t)) * ∑ t, ind (w t) =
        ∑ t, (∏ t, μ (w t)) * ind (w t) := fun w => Finset.mul_sum _ _ _
    simp only [e]
    rw [Finset.sum_comm]
    have e2 : ∀ t0 : Fin m, ∑ w : Fin m → γ, (∏ t, μ (w t)) * ind (w t0) = q := by
      intro t0; rw [sum_prod_ind μ ind hμ1 t0, hq]
    simp only [e2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hS1 : ∑ w : Fin m → γ, (∏ t, μ (w t)) * (∑ t, ind (w t)) ^ 2 =
      m * q + (m * m - m) * q ^ 2 := by
    have e : ∀ w : Fin m → γ, (∏ t, μ (w t)) * (∑ t, ind (w t)) ^ 2 =
        ∑ t1, ∑ t2, (∏ t, μ (w t)) * (ind (w t1) * ind (w t2)) := by
      intro w
      rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun t1 _ => Finset.mul_sum _ _ _
    simp only [e]
    rw [Finset.sum_comm]
    have e2 : ∀ t1 : Fin m, ∑ w : Fin m → γ, ∑ t2, (∏ t, μ (w t)) * (ind (w t1) * ind (w t2)) =
        ∑ t2 : Fin m, (if t1 = t2 then q else q ^ 2) := by
      intro t1
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun t2 _ => ?_
      rw [sum_prod_ind2 μ ind hμ1 hind t1 t2, hq]
    simp only [e2]
    have e3 : ∀ t1 : Fin m, ∑ t2 : Fin m, (if t1 = t2 then q else q ^ 2) = q + (m - 1) * q ^ 2 := by
      intro t1
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ t1), if_pos rfl]
      rw [Finset.sum_congr rfl fun t2 ht2 => if_neg (Ne.symm (Finset.ne_of_mem_erase ht2))]
      rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      rcases Nat.eq_zero_or_pos m with hm | hm
      · exact absurd t1.isLt (by omega)
      · rw [Nat.cast_sub hm]; push_cast; ring
    simp only [e3, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  calc ∑ w : Fin m → γ, (∏ t, μ (w t)) * (∑ t, ind (w t) - m * q) ^ 2
      = ∑ w : Fin m → γ, ((∏ t, μ (w t)) * (∑ t, ind (w t)) ^ 2 -
          2 * (m * q) * ((∏ t, μ (w t)) * ∑ t, ind (w t)) + (m * q) ^ 2 * ∏ t, μ (w t)) := by
        refine Finset.sum_congr rfl fun w _ => ?_
        ring
    _ = (∑ w : Fin m → γ, (∏ t, μ (w t)) * (∑ t, ind (w t)) ^ 2) -
          2 * (m * q) * (∑ w : Fin m → γ, (∏ t, μ (w t)) * ∑ t, ind (w t)) +
          (m * q) ^ 2 * ∑ w : Fin m → γ, ∏ t, μ (w t) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ = m * q * (1 - q) := by
        rw [hS1, hS2, hS0]
        ring

/-- **Chebyshev bound** for the lower tail of the number of successes. -/
theorem count_lower_tail (hμ0 : ∀ g, 0 ≤ μ g) (hμ1 : ∑ g, μ g = 1)
    (hind : ∀ x, ind x * ind x = ind x) (k : ℝ) (hk : k < m * ∑ x, μ x * ind x) :
    ∑ w : Fin m → γ, (∏ t, μ (w t)) * (if ∑ t, ind (w t) < k then 1 else 0) ≤
      m * (∑ x, μ x * ind x) * (1 - ∑ x, μ x * ind x) / (m * (∑ x, μ x * ind x) - k) ^ 2 := by
  set q := ∑ x, μ x * ind x with hq
  have hpos : 0 < m * q - k := by linarith
  rw [← variance_count μ ind hμ1 hind, Finset.sum_div]
  refine Finset.sum_le_sum fun w _ => ?_
  have hP : 0 ≤ ∏ t, μ (w t) := Finset.prod_nonneg fun t _ => hμ0 _
  split_ifs with h
  · rw [mul_one, mul_div_assoc]
    refine le_mul_of_one_le_right hP ?_
    rw [one_le_div (by positivity)]
    nlinarith
  · rw [mul_zero]
    positivity

end Cheb

end FKR

end Mod_FKR_Cheb

set_option autoImplicit false

open QAlgorithms QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Intakenext100.P17

noncomputable section

namespace BB84Sift

/-- Uniform law on a pair of bits. -/
def μ2 : Bool × Bool → ℝ := fun _ => 1 / 4

/-- Indicator of matching bases. -/
def ind2 : Bool × Bool → ℝ := fun p => if p.1 = p.2 then 1 else 0

lemma μ2_sum : ∑ g, μ2 g = 1 := by
  simp [μ2]

lemma ind2_sq (x : Bool × Bool) : ind2 x * ind2 x = ind2 x := by
  unfold ind2; split_ifs <;> norm_num

lemma q2 : ∑ x, μ2 x * ind2 x = 1 / 2 := by
  simp [μ2, ind2, Fintype.sum_prod_type]
  norm_num

/-- Pairs of basis strings as strings of pairs. -/
def pairEq (N : ℕ) : (Fin N → Bool × Bool) ≃ Qubits N × Qubits N :=
  Equiv.arrowProdEquivProdArrow (Fin N) (fun _ => Bool) (fun _ => Bool)

lemma matches_eq {N : ℕ} (w : Fin N → Bool × Bool) :
    (basisMatches (pairEq N w).1 (pairEq N w).2 : ℝ) = ∑ t, ind2 (w t) := by
  unfold basisMatches ind2
  rw [Finset.natCast_card_filter]
  rfl

lemma prod_μ2 {N : ℕ} (w : Fin N → Bool × Bool) :
    ∏ t, μ2 (w t) = ((2 : ℝ) ^ (2 * N))⁻¹ := by
  simp only [μ2, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [pow_mul, ← inv_pow]
  norm_num

lemma sifting_eq (n N : ℕ) :
    siftingSuccess n N = 1 - ∑ w : Fin N → Bool × Bool, (∏ t, μ2 (w t)) *
      (if ∑ t, ind2 (w t) < (2 * n : ℕ) then 1 else 0) := by
  have h1 : ∑ w : Fin N → Bool × Bool, ∏ t, μ2 (w t) = 1 := FKR.sum_prod_one μ2 μ2_sum
  have e : ∀ w : Fin N → Bool × Bool,
      ((2 : ℝ) ^ (2 * N))⁻¹ * (if 2 * n ≤ basisMatches (pairEq N w).1 (pairEq N w).2 then 1 else 0) =
        (∏ t, μ2 (w t)) - (∏ t, μ2 (w t)) *
          (if ∑ t, ind2 (w t) < (2 * n : ℕ) then 1 else 0) := by
    intro w
    rw [prod_μ2]
    have hm := matches_eq w
    by_cases h : 2 * n ≤ basisMatches (pairEq N w).1 (pairEq N w).2
    · have h' : ¬ (∑ t, ind2 (w t) < ((2 * n : ℕ) : ℝ)) := by
        rw [not_lt, ← hm]; exact_mod_cast h
      simp only [h, h', if_true, if_false]
      ring
    · have h' : ∑ t, ind2 (w t) < ((2 * n : ℕ) : ℝ) := by
        rw [← hm]; exact_mod_cast not_le.mp h
      simp only [h, h', if_true, if_false]
      ring
  unfold siftingSuccess
  rw [← Fintype.sum_prod_type', ← (pairEq N).sum_comp, Finset.mul_sum]
  simp only [e]
  rw [Finset.sum_sub_distrib, h1]

lemma sifting_le_one (n N : ℕ) : siftingSuccess n N ≤ 1 := by
  rw [sifting_eq]
  have : 0 ≤ ∑ w : Fin N → Bool × Bool, (∏ t, μ2 (w t)) *
      (if ∑ t, ind2 (w t) < (2 * n : ℕ) then 1 else 0) := by
    refine Finset.sum_nonneg fun w _ => mul_nonneg (Finset.prod_nonneg fun t _ => ?_) ?_
    · unfold μ2; norm_num
    · split_ifs <;> norm_num
  linarith

lemma sifting_ge (n N : ℕ) (hN : (2 * n : ℝ) < N * (1 / 2)) :
    1 - N * (1 / 2) * (1 - 1 / 2) / (N * (1 / 2) - (2 * n : ℝ)) ^ 2 ≤ siftingSuccess n N := by
  rw [sifting_eq]
  have h := FKR.count_lower_tail (m := N) μ2 ind2 (fun g => by unfold μ2; norm_num) μ2_sum ind2_sq
    ((2 * n : ℕ) : ℝ) (by rw [q2]; push_cast; exact hN)
  rw [q2] at h
  push_cast at h ⊢
  linarith

lemma signalCount_ge (gamma : ℝ) (hgamma : 0 < gamma) (n : ℕ) :
    (4 + gamma) * n ≤ (signalCount gamma n : ℝ) :=
  Nat.le_ceil _

lemma signalCount_le (gamma : ℝ) (hgamma : 0 < gamma) (n : ℕ) :
    (signalCount gamma n : ℝ) ≤ (4 + gamma) * n + 1 := by
  unfold signalCount
  have := Nat.ceil_lt_add_one (show 0 ≤ (4 + gamma) * (n : ℝ) by positivity)
  linarith

lemma gap_bound (gamma : ℝ) (hgamma : 0 < gamma) (n : ℕ) (hn : 1 ≤ n) :
    1 - (5 + gamma) / (gamma ^ 2 * n) ≤ siftingSuccess n (signalCount gamma n) := by
  set N := signalCount gamma n with hNdef
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hN1 := signalCount_ge gamma hgamma n
  have hN2 := signalCount_le gamma hgamma n
  rw [← hNdef] at hN1 hN2
  have hgap : gamma * n / 2 ≤ (N : ℝ) * (1 / 2) - 2 * n := by linarith
  have hgap0 : 0 < gamma * n / 2 := by positivity
  have hN : (2 * n : ℝ) < N * (1 / 2) := by linarith
  refine le_trans ?_ (sifting_ge n N hN)
  have hsq : (gamma * n / 2) ^ 2 ≤ ((N : ℝ) * (1 / 2) - 2 * n) ^ 2 :=
    pow_le_pow_left₀ hgap0.le hgap 2
  have hnum : (N : ℝ) * (1 / 2) * (1 - 1 / 2) ≤ (5 + gamma) * n / 4 := by nlinarith
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have key : (N : ℝ) * (1 / 2) * (1 - 1 / 2) / ((N : ℝ) * (1 / 2) - 2 * n) ^ 2 ≤
      (5 + gamma) / (gamma ^ 2 * n) := by
    calc (N : ℝ) * (1 / 2) * (1 - 1 / 2) / ((N : ℝ) * (1 / 2) - 2 * n) ^ 2
        ≤ ((5 + gamma) * n / 4) / ((N : ℝ) * (1 / 2) - 2 * n) ^ 2 :=
          div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ ((5 + gamma) * n / 4) / (gamma * n / 2) ^ 2 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hsq
      _ = (5 + gamma) / (gamma ^ 2 * n) := by
          field_simp
          ring
  linarith

end BB84Sift

open BB84Sift in
theorem solution (gamma : ℝ) (hgamma : 0 < gamma) :
    Filter.Tendsto (fun n : ℕ => siftingSuccess n (signalCount gamma n))
      Filter.atTop (nhds (1 : ℝ)) := by
  have hlim : Filter.Tendsto (fun n : ℕ => 1 - (5 + gamma) / (gamma ^ 2) / (n : ℝ))
      Filter.atTop (nhds (1 : ℝ)) := by
    have := (tendsto_const_div_atTop_nhds_zero_nat ((5 + gamma) / gamma ^ 2)).const_sub (1 : ℝ)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim tendsto_const_nhds ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have := gap_bound gamma hgamma n hn
    rw [div_div] at *
    exact this
  · exact Filter.Eventually.of_forall fun n => sifting_le_one n _
