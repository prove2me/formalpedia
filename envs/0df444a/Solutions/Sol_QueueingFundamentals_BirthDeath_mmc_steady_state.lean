-- Prove2me | solution 1 for QueueingFundamentals.BirthDeath.mmc_steady_state
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T00:33:32.657029+00:00
-- url     : https://prove2.me/submissions/f1554dbe-6f1b-439c-a6c3-1a48bc367dc9

import Mathlib
import Definitions.Def_QueueingFundamentals_BirthDeath_Balance

set_option autoImplicit false

namespace MMCAux

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


theorem mmc_q (lam mu : ℝ) (c : ℕ) (hmu : 0 < mu) (hc : 1 ≤ c) (n : ℕ) :
    bdProd (fun _ => lam) (mmcDeath mu c) n =
      if n < c then lam ^ n / ((n.factorial : ℝ) * mu ^ n)
      else lam ^ n / ((c : ℝ) ^ (n - c) * (c.factorial : ℝ) * mu ^ n) := by
  have hcpos : (0 : ℝ) < c := by exact_mod_cast (show 0 < c by omega)
  induction n with
  | zero => rw [if_pos (by omega), bdProd_zero]; simp
  | succ k ih =>
    rw [bdProd_succ, ih]
    unfold mmcDeath
    by_cases h1 : k + 1 < c
    · have hk : k < c := by omega
      rw [if_pos hk, if_pos h1, min_eq_left h1.le, Nat.factorial_succ]
      push_cast
      field_simp
      ring
    · by_cases h2 : k < c
      · have hck : c = k + 1 := by omega
        subst hck
        rw [if_pos h2, if_neg h1, min_self, Nat.sub_self, Nat.factorial_succ]
        push_cast
        field_simp
        ring
      · rw [if_neg h2, if_neg h1, min_eq_right (by omega)]
        have he : k + 1 - c = (k - c) + 1 := by omega
        rw [he, pow_succ]
        field_simp
        ring

theorem mmc_tail (lam mu : ℝ) (c : ℕ) (r ρ : ℝ) (hmu : 0 < mu) (hc : 1 ≤ c)
    (hr : r = lam / mu) (hρ : ρ = r / c) (k : ℕ) :
    bdProd (fun _ => lam) (mmcDeath mu c) (k + c) =
      r ^ c / (c.factorial : ℝ) * ρ ^ k := by
  have hcpos : (0 : ℝ) < c := by exact_mod_cast (show 0 < c by omega)
  rw [mmc_q lam mu c hmu hc, if_neg (by omega), Nat.add_sub_cancel, hρ, hr]
  rw [div_pow, div_pow, div_pow, pow_add, pow_add]
  field_simp

theorem mmc_head (lam mu : ℝ) (c : ℕ) (r : ℝ) (hmu : 0 < mu) (hc : 1 ≤ c)
    (hr : r = lam / mu) :
    ∑ n ∈ Finset.range c, bdProd (fun _ => lam) (mmcDeath mu c) n =
      ∑ n ∈ Finset.range c, r ^ n / (n.factorial : ℝ) := by
  apply Finset.sum_congr rfl
  intro n hn
  rw [mmc_q lam mu c hmu hc, if_pos (Finset.mem_range.mp hn), hr, div_pow]
  field_simp

theorem mmc_hasSum (lam mu : ℝ) (c : ℕ) (r ρ : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (hc : 1 ≤ c)
    (hr : r = lam / mu) (hρ : ρ = r / c) (h1 : ρ < 1) :
    HasSum (fun n : ℕ => bdProd (fun _ => lam) (mmcDeath mu c) (n + 1))
      ((r ^ c / ((c.factorial : ℝ) * (1 - ρ)) +
        ∑ n ∈ Finset.range c, r ^ n / (n.factorial : ℝ)) - 1) := by
  have hcpos : (0 : ℝ) < c := by exact_mod_cast (show 0 < c by omega)
  have hρ0 : 0 ≤ ρ := by
    rw [hρ, hr]; positivity
  have hgeo := (hasSum_geometric_of_lt_one hρ0 h1).mul_left (r ^ c / (c.factorial : ℝ))
  have htail : HasSum (fun k : ℕ => bdProd (fun _ => lam) (mmcDeath mu c) (k + c))
      ((r ^ c / ((c.factorial : ℝ) * (1 - ρ)) +
        ∑ n ∈ Finset.range c, r ^ n / (n.factorial : ℝ)) -
        ∑ i ∈ Finset.range c, bdProd (fun _ => lam) (mmcDeath mu c) i) := by
    rw [mmc_head lam mu c r hmu hc hr]
    have hne : (1 - ρ) ≠ 0 := by linarith
    have hv : r ^ c / ((c.factorial : ℝ) * (1 - ρ)) +
        ∑ n ∈ Finset.range c, r ^ n / (n.factorial : ℝ) -
        ∑ n ∈ Finset.range c, r ^ n / (n.factorial : ℝ) =
        r ^ c / (c.factorial : ℝ) * (1 - ρ)⁻¹ := by
      rw [add_sub_cancel_right]; field_simp
    rw [hv]
    refine hgeo.congr_fun ?_
    intro k
    exact mmc_tail lam mu c r ρ hmu hc hr hρ k
  have hall := (hasSum_nat_add_iff' c).mp htail
  have := (hasSum_nat_add_iff' 1).mpr hall
  simpa [Finset.sum_range_one, bdProd_zero] using this

theorem mmc_rho_lt (lam mu : ℝ) (c : ℕ) (r ρ : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (hc : 1 ≤ c)
    (hr : r = lam / mu) (hρ : ρ = r / c)
    (hs : Summable (fun n : ℕ => bdProd (fun _ => lam) (mmcDeath mu c) (n + 1))) : ρ < 1 := by
  have hcpos : (0 : ℝ) < c := by exact_mod_cast (show 0 < c by omega)
  have hrpos : 0 < r := by rw [hr]; positivity
  have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
  have hs0 : Summable (fun n : ℕ => bdProd (fun _ => lam) (mmcDeath mu c) n) :=
    (summable_nat_add_iff 1).mp hs
  have hsc : Summable (fun k : ℕ => bdProd (fun _ => lam) (mmcDeath mu c) (k + c)) :=
    (summable_nat_add_iff c).mpr hs0
  have hK : r ^ c / (c.factorial : ℝ) ≠ 0 := by positivity
  have hg : Summable (fun k : ℕ => ρ ^ k) := by
    have := hsc.mul_left (r ^ c / (c.factorial : ℝ))⁻¹
    refine this.congr ?_
    intro k
    rw [mmc_tail lam mu c r ρ hmu hc hr hρ k]
    field_simp
  have := summable_geometric_iff_norm_lt_one.mp hg
  rw [Real.norm_eq_abs, abs_of_nonneg hρ0] at this
  exact this

end MMCAux

open QueueingFundamentals.BirthDeath in
theorem solution (lam mu : ℝ) (c : ℕ) (r ρ : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (hc : 1 ≤ c) (hr : r = lam / mu) (hρ : ρ = r / c) :
    ((∃ p : ℕ → ℝ, IsSteadyState (fun _ => lam) (mmcDeath mu c) p) ↔ ρ < 1) ∧
      (ρ < 1 → ∀ p : ℕ → ℝ, IsSteadyState (fun _ => lam) (mmcDeath mu c) p ↔
        ((∀ n : ℕ, p n =
            if n < c then lam ^ n / ((n.factorial : ℝ) * mu ^ n) * p 0
            else lam ^ n / ((c : ℝ) ^ (n - c) * (c.factorial : ℝ) * mu ^ n) * p 0) ∧
          p 0 = (r ^ c / ((c.factorial : ℝ) * (1 - ρ)) +
            ∑ n ∈ Finset.range c, r ^ n / (n.factorial : ℝ))⁻¹)) := by
  have hlam' : ∀ n : ℕ, 0 ≤ (fun _ : ℕ => lam) n := fun _ => hlam.le
  have hmu' : ∀ n : ℕ, 1 ≤ n → 0 < mmcDeath mu c n := by
    intro n hn
    unfold mmcDeath
    have : (0 : ℝ) < ((min n c : ℕ) : ℝ) := by exact_mod_cast (show 0 < min n c by omega)
    positivity
  refine ⟨⟨fun ⟨p, hp⟩ => MMCAux.mmc_rho_lt lam mu c r ρ hlam hmu hc hr hρ
      (MMCAux.forward _ _ hmu' p hp).1, fun h1 => ?_⟩, fun h1 p => ?_⟩
  · have hs := (MMCAux.mmc_hasSum lam mu c r ρ hlam hmu hc hr hρ h1).summable
    refine ⟨fun n => (1 + ∑' n : ℕ, bdProd (fun _ => lam) (mmcDeath mu c) (n + 1))⁻¹ *
      bdProd (fun _ => lam) (mmcDeath mu c) n,
      MMCAux.backward _ _ hlam' hmu' _ hs ?_ ?_⟩
    · simp [MMCAux.bdProd_zero]
    · intro n
      simp [MMCAux.bdProd_zero]
  · have hS := MMCAux.mmc_hasSum lam mu c r ρ hlam hmu hc hr hρ h1
    have htsum : 1 + ∑' n : ℕ, bdProd (fun _ => lam) (mmcDeath mu c) (n + 1) =
        r ^ c / ((c.factorial : ℝ) * (1 - ρ)) +
          ∑ n ∈ Finset.range c, r ^ n / (n.factorial : ℝ) := by
      rw [hS.tsum_eq]; ring
    have hform : ∀ n : ℕ, (p n = p 0 * bdProd (fun _ => lam) (mmcDeath mu c) n) ↔
        (p n = if n < c then lam ^ n / ((n.factorial : ℝ) * mu ^ n) * p 0
            else lam ^ n / ((c : ℝ) ^ (n - c) * (c.factorial : ℝ) * mu ^ n) * p 0) := by
      intro n
      rw [MMCAux.mmc_q lam mu c hmu hc n]
      split_ifs <;> rw [mul_comm]
    constructor
    · intro hp
      obtain ⟨_, h2, h3⟩ := MMCAux.forward _ _ hmu' p hp
      exact ⟨fun n => (hform n).mp (h3 n), by rw [h2, htsum]⟩
    · rintro ⟨h3, h2⟩
      exact MMCAux.backward _ _ hlam' hmu' p hS.summable (by rw [htsum]; exact h2)
        (fun n => (hform n).mpr (h3 n))
