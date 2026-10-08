-- Prove2me | solution 1 for QueueingFundamentals.BirthDeath.birth_death_steady_state
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T17:25:39.823356+00:00
-- url     : https://prove2.me/submissions/1eb96350-6d24-497d-98a7-26dd87fd18ae

import Mathlib
import Definitions.Def_QueueingFundamentals_BirthDeath_Balance

set_option autoImplicit false

namespace BDSteadyAux

open QueueingFundamentals.BirthDeath

theorem bdProd_zero (lam mu : ℕ → ℝ) : bdProd lam mu 0 = 1 := by
  simp [bdProd]

theorem bdProd_succ (lam mu : ℕ → ℝ) (n : ℕ) :
    bdProd lam mu (n + 1) = bdProd lam mu n * (lam n / mu (n + 1)) := by
  unfold bdProd
  rw [Finset.prod_Icc_succ_top (by omega)]
  simp

theorem bdProd_nonneg (lam mu : ℕ → ℝ) (hlam : ∀ n : ℕ, 0 ≤ lam n)
    (hmu : ∀ n : ℕ, 1 ≤ n → 0 < mu n) (n : ℕ) : 0 ≤ bdProd lam mu n := by
  unfold bdProd
  apply Finset.prod_nonneg
  intro i hi
  exact div_nonneg (hlam _) (hmu i (Finset.mem_Icc.mp hi).1).le

theorem cut_of_balanced (lam mu p : ℕ → ℝ) (h : IsBalanced lam mu p) (n : ℕ) :
    lam n * p n = mu (n + 1) * p (n + 1) := by
  induction n with
  | zero => simpa using h.2
  | succ k ih =>
    have h1 := h.1 (k + 1) (by omega)
    simp only [Nat.add_sub_cancel] at h1
    linarith

theorem balanced_of_cut (lam mu p : ℕ → ℝ)
    (h : ∀ n : ℕ, lam n * p n = mu (n + 1) * p (n + 1)) : IsBalanced lam mu p := by
  refine ⟨?_, by simpa using h 0⟩
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h1 := h m
  have h2 := h (m + 1)
  simp only [Nat.add_sub_cancel]
  linarith

theorem form_of_cut (lam mu p : ℕ → ℝ) (hmu : ∀ n : ℕ, 1 ≤ n → 0 < mu n)
    (h : ∀ n : ℕ, lam n * p n = mu (n + 1) * p (n + 1)) (n : ℕ) :
    p n = p 0 * bdProd lam mu n := by
  induction n with
  | zero => simp [bdProd_zero]
  | succ k ih =>
    have hm := hmu (k + 1) (by omega)
    have hp : p (k + 1) = lam k * p k / mu (k + 1) := by
      rw [eq_div_iff hm.ne']
      linear_combination -(h k)
    rw [hp, bdProd_succ, ih]
    field_simp

theorem forward (lam mu : ℕ → ℝ) (hmu : ∀ n : ℕ, 1 ≤ n → 0 < mu n) (p : ℕ → ℝ)
    (hp : IsSteadyState lam mu p) :
    Summable (fun n : ℕ => bdProd lam mu (n + 1)) ∧
      p 0 = (1 + ∑' n : ℕ, bdProd lam mu (n + 1))⁻¹ ∧
      ∀ n : ℕ, p n = p 0 * bdProd lam mu n := by
  obtain ⟨hnn, hsum, hbal⟩ := hp
  have hform : ∀ n : ℕ, p n = p 0 * bdProd lam mu n :=
    form_of_cut lam mu p hmu (cut_of_balanced lam mu p hbal)
  have hp0 : 0 < p 0 := by
    rcases (hnn 0).lt_or_eq with h | h
    · exact h
    · exfalso
      have hz : p = fun _ => 0 := by
        funext n; rw [hform n, ← h]; ring
      rw [hz] at hsum
      have := hsum.unique hasSum_zero
      norm_num at this
  have htail : HasSum (fun n : ℕ => p (n + 1)) (1 - p 0) := by
    have := (hasSum_nat_add_iff' (f := p) 1 (g := 1)).mpr hsum
    simpa using this
  have hsumm : Summable (fun n : ℕ => bdProd lam mu (n + 1)) := by
    have hs : Summable (fun n : ℕ => p (n + 1) / p 0) := htail.summable.div_const _
    refine hs.congr ?_
    intro n
    rw [hform (n + 1)]
    field_simp
  refine ⟨hsumm, ?_, hform⟩
  have h2 : HasSum (fun n : ℕ => p (n + 1)) (p 0 * ∑' n : ℕ, bdProd lam mu (n + 1)) := by
    have := hsumm.hasSum.mul_left (p 0)
    refine this.congr_fun ?_
    intro n
    exact hform (n + 1)
  have heq := htail.unique h2
  have hS : 0 ≤ ∑' n : ℕ, bdProd lam mu (n + 1) := by
    apply tsum_nonneg
    intro n
    rw [show bdProd lam mu (n + 1) = p (n + 1) / p 0 by rw [hform (n + 1)]; field_simp]
    exact div_nonneg (hnn _) hp0.le
  have h1S : (0 : ℝ) < 1 + ∑' n : ℕ, bdProd lam mu (n + 1) := by linarith
  exact eq_inv_of_mul_eq_one_left (by linear_combination -heq)

theorem backward (lam mu : ℕ → ℝ) (hlam : ∀ n : ℕ, 0 ≤ lam n)
    (hmu : ∀ n : ℕ, 1 ≤ n → 0 < mu n) (p : ℕ → ℝ)
    (hsumm : Summable (fun n : ℕ => bdProd lam mu (n + 1)))
    (hp0 : p 0 = (1 + ∑' n : ℕ, bdProd lam mu (n + 1))⁻¹)
    (hform : ∀ n : ℕ, p n = p 0 * bdProd lam mu n) : IsSteadyState lam mu p := by
  have hS : 0 ≤ ∑' n : ℕ, bdProd lam mu (n + 1) :=
    tsum_nonneg (fun n => bdProd_nonneg lam mu hlam hmu (n + 1))
  have h1S : (0 : ℝ) < 1 + ∑' n : ℕ, bdProd lam mu (n + 1) := by linarith
  have hpos : 0 < p 0 := by rw [hp0]; exact inv_pos.mpr h1S
  have hmul : p 0 * (1 + ∑' n : ℕ, bdProd lam mu (n + 1)) = 1 := by
    rw [hp0]; exact inv_mul_cancel₀ h1S.ne'
  refine ⟨?_, ?_, ?_⟩
  · intro n
    rw [hform n]
    exact mul_nonneg hpos.le (bdProd_nonneg lam mu hlam hmu n)
  · have h2 : HasSum (fun n : ℕ => p (n + 1)) (p 0 * ∑' n : ℕ, bdProd lam mu (n + 1)) := by
      have := hsumm.hasSum.mul_left (p 0)
      refine this.congr_fun ?_
      intro n
      exact hform (n + 1)
    have h3 : p 0 * ∑' n : ℕ, bdProd lam mu (n + 1) = 1 - ∑ i ∈ Finset.range 1, p i := by
      simp only [Finset.sum_range_one]
      linarith
    rw [h3] at h2
    exact (hasSum_nat_add_iff' 1).mp h2
  · apply balanced_of_cut
    intro n
    have hm := hmu (n + 1) (by omega)
    rw [hform (n + 1), hform n, bdProd_succ]
    field_simp

end BDSteadyAux

open QueueingFundamentals.BirthDeath in
theorem solution (lam mu : ℕ → ℝ) (hlam : ∀ n : ℕ, 0 ≤ lam n)
    (hmu : ∀ n : ℕ, 1 ≤ n → 0 < mu n) :
    ((∃ p : ℕ → ℝ, IsSteadyState lam mu p) ↔
        Summable (fun n : ℕ => bdProd lam mu (n + 1))) ∧
      ∀ p : ℕ → ℝ, IsSteadyState lam mu p ↔
        (Summable (fun n : ℕ => bdProd lam mu (n + 1)) ∧
          p 0 = (1 + ∑' n : ℕ, bdProd lam mu (n + 1))⁻¹ ∧
          ∀ n : ℕ, p n = p 0 * bdProd lam mu n) := by
  refine ⟨⟨fun ⟨p, hp⟩ => (BDSteadyAux.forward lam mu hmu p hp).1, fun hs => ?_⟩, fun p =>
    ⟨BDSteadyAux.forward lam mu hmu p, fun ⟨h1, h2, h3⟩ =>
      BDSteadyAux.backward lam mu hlam hmu p h1 h2 h3⟩⟩
  refine ⟨fun n => (1 + ∑' n : ℕ, bdProd lam mu (n + 1))⁻¹ * bdProd lam mu n,
    BDSteadyAux.backward lam mu hlam hmu _ hs ?_ ?_⟩
  · simp [BDSteadyAux.bdProd_zero]
  · intro n
    simp [BDSteadyAux.bdProd_zero]
