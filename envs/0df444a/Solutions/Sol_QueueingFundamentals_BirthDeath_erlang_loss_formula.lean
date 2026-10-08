-- Prove2me | solution 1 for QueueingFundamentals.BirthDeath.erlang_loss_formula
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T15:15:28.682001+00:00
-- url     : https://prove2.me/submissions/ce703a0d-2fbd-4886-8055-b4fa426f6cf9

import Mathlib
import Definitions.Def_QueueingFundamentals_BirthDeath_Balance
import Definitions.Def_QueueingFundamentals_BirthDeath_Erlang



namespace QueueingFundamentals.BirthDeath

lemma qf_detailed_of_balanced {lam mu p : ℕ → ℝ} (h : IsBalanced lam mu p) :
    ∀ n, lam n * p n = mu (n + 1) * p (n + 1) := by
  intro n
  induction n with
  | zero => simpa using h.2
  | succ k ih =>
    have := h.1 (k + 1) (by omega)
    simp only [Nat.add_sub_cancel] at this
    linear_combination this + ih

lemma qf_balanced_of_detailed {lam mu p : ℕ → ℝ}
    (h : ∀ n, lam n * p n = mu (n + 1) * p (n + 1)) : IsBalanced lam mu p := by
  refine ⟨fun n hn => ?_, by simpa using h 0⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  linear_combination h (m + 1) - h m

lemma qf_mmc_low {lam mu r : ℝ} {c : ℕ} {p : ℕ → ℝ} (hmu : 0 < mu) (hr : lam = r * mu)
    (h : ∀ n, n < c → lam * p n = mmcDeath mu c (n + 1) * p (n + 1)) :
    ∀ n, n ≤ c → p n = r ^ n / (n.factorial : ℝ) * p 0 := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have h1 := h k (by omega)
    have hmin : min (k + 1) c = k + 1 := by omega
    simp only [mmcDeath, hmin] at h1
    have hmu' : mu ≠ 0 := hmu.ne'
    have hk1 : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hp : p (k + 1) = r * p k / ((k + 1 : ℕ) : ℝ) := by
      rw [eq_div_iff hk1]
      apply mul_right_cancel₀ hmu'
      rw [hr] at h1
      linear_combination -h1
    rw [hp, ih (by omega), Nat.factorial_succ, pow_succ]
    push_cast
    field_simp

lemma qf_mmc_high {lam mu r ρ : ℝ} {c : ℕ} {p : ℕ → ℝ} (hmu : 0 < mu) (hc : 1 ≤ c)
    (hr : lam = r * mu) (hρ : r = ρ * c)
    (h : ∀ n, lam * p n = mmcDeath mu c (n + 1) * p (n + 1)) :
    ∀ k, p (c + k) = r ^ c / (c.factorial : ℝ) * ρ ^ k * p 0 := by
  intro k
  induction k with
  | zero => simpa using qf_mmc_low hmu hr (fun n _ => h n) c le_rfl
  | succ k ih =>
    have h1 := h (c + k)
    have hmin : min (c + k + 1) c = c := by omega
    simp only [mmcDeath, hmin] at h1
    have hcpos : (0 : ℝ) < c := by exact_mod_cast hc
    have hmu' : mu ≠ 0 := hmu.ne'
    have hc' : (c : ℝ) ≠ 0 := hcpos.ne'
    have hp : p (c + (k + 1)) = ρ * p (c + k) := by
      apply mul_left_cancel₀ (mul_ne_zero hc' hmu')
      rw [← add_assoc, ← h1, hr, hρ]; ring
    rw [hp, ih]
    ring

/-- the full structure of an M/M/c steady state -/
lemma qf_mmc_data (lam mu r ρ : ℝ) (c : ℕ) (hlam : 0 < lam) (hmu : 0 < mu) (hc : 1 ≤ c)
    (hr : r = lam / mu) (hρ : ρ = r / c)
    (hρ1 : ρ < 1) (p : ℕ → ℝ)
    (hp : IsSteadyState (fun _ => lam) (mmcDeath mu c) p) :
    (∀ n, n ≤ c → p n = r ^ n / (n.factorial : ℝ) * p 0) ∧
    (∀ k, p (c + k) = r ^ c / (c.factorial : ℝ) * ρ ^ k * p 0) ∧
    ∑ n ∈ Finset.range c, p n =
      1 - r ^ c * p 0 / ((c.factorial : ℝ) * (1 - ρ)) := by
  have hd := qf_detailed_of_balanced hp.2.2
  have hcpos : (0 : ℝ) < c := by exact_mod_cast hc
  have hr' : lam = r * mu := by rw [hr]; field_simp
  have hρ' : r = ρ * c := by rw [hρ]; field_simp
  have hlow := qf_mmc_low hmu hr' (fun n _ => hd n)
  have hhigh := qf_mmc_high hmu hc hr' hρ' hd
  refine ⟨hlow, hhigh, ?_⟩
  have hρ0 : 0 ≤ ρ := by rw [hρ, hr]; positivity
  have hg : HasSum (fun k => p (k + c)) (r ^ c / (c.factorial : ℝ) * p 0 * (1 - ρ)⁻¹) := by
    have := (hasSum_geometric_of_lt_one hρ0 hρ1).mul_left (r ^ c / (c.factorial : ℝ) * p 0)
    have e : (fun k => p (k + c)) = fun k => r ^ c / (c.factorial : ℝ) * p 0 * ρ ^ k := by
      funext k; rw [add_comm, hhigh k]; ring
    rw [e]; exact this
  have h2 := (hasSum_nat_add_iff' c).mpr hp.2.1
  have := h2.unique hg
  have h1ρ : (1 - ρ) ≠ 0 := by linarith
  have hfac : (c.factorial : ℝ) ≠ 0 := by positivity
  have e2 : r ^ c * p 0 / ((c.factorial : ℝ) * (1 - ρ)) =
      r ^ c / (c.factorial : ℝ) * p 0 * (1 - ρ)⁻¹ := by field_simp
  rw [e2]; linarith

theorem mmc_queue_length_core (lam mu : ℝ) (c : ℕ) (r ρ : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (hc : 1 ≤ c) (hr : r = lam / mu) (hρ : ρ = r / c) (hρ1 : ρ < 1) (p : ℕ → ℝ)
    (hp : IsSteadyState (fun _ => lam) (mmcDeath mu c) p) :
    HasSum (fun n : ℕ => if c + 1 ≤ n then ((n : ℝ) - c) * p n else 0)
      (r ^ c * ρ / ((c.factorial : ℝ) * (1 - ρ) ^ 2) * p 0) := by
  obtain ⟨-, hhigh, -⟩ := qf_mmc_data lam mu r ρ c hlam hmu hc hr hρ hρ1 p hp
  have hρ0 : 0 ≤ ρ := by rw [hρ, hr]; positivity
  have hn : ‖ρ‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hρ0]; exact hρ1
  have hg := (hasSum_coe_mul_geometric_of_norm_lt_one hn).mul_left
    (r ^ c / (c.factorial : ℝ) * p 0)
  apply (hasSum_nat_add_iff' c).mp
  have hz : ∑ i ∈ Finset.range c,
      (if c + 1 ≤ i then ((i : ℝ) - c) * p i else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_range] at hi
    rw [if_neg (by omega)]
  rw [hz, sub_zero]
  have e : (fun k => if c + 1 ≤ k + c then (((k + c : ℕ) : ℝ) - c) * p (k + c) else 0) =
      fun k : ℕ => r ^ c / (c.factorial : ℝ) * p 0 * ((k : ℝ) * ρ ^ k) := by
    funext k
    by_cases hk : c + 1 ≤ k + c
    · rw [if_pos hk, add_comm k c, hhigh k]; push_cast; ring
    · rw [if_neg hk]
      have : k = 0 := by omega
      subst this; simp
  have h1ρ : (1 - ρ) ≠ 0 := by linarith
  have hfac : (c.factorial : ℝ) ≠ 0 := by positivity
  have e2 : r ^ c * ρ / ((c.factorial : ℝ) * (1 - ρ) ^ 2) * p 0 =
      r ^ c / (c.factorial : ℝ) * p 0 * (ρ / (1 - ρ) ^ 2) := by field_simp
  rw [e2]
  exact e ▸ hg

theorem erlang_c_formula_core (lam mu : ℝ) (c : ℕ) (r ρ : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (hc : 1 ≤ c) (hr : r = lam / mu) (hρ : ρ = r / c) (hρ1 : ρ < 1) (p : ℕ → ℝ)
    (hp : IsSteadyState (fun _ => lam) (mmcDeath mu c) p) :
    ∑ n ∈ Finset.range c, p n = 1 - r ^ c * p 0 / ((c.factorial : ℝ) * (1 - ρ)) ∧
      1 - ∑ n ∈ Finset.range c, p n = erlangC c r := by
  obtain ⟨hlow, -, hsum⟩ := qf_mmc_data lam mu r ρ c hlam hmu hc hr hρ hρ1 p hp
  refine ⟨hsum, ?_⟩
  have hr0 : 0 < r := by rw [hr]; positivity
  have h1ρ : 0 < 1 - ρ := by linarith
  have hfac : (0 : ℝ) < c.factorial := by positivity
  have hT : r ^ c / ((c.factorial : ℝ) * (1 - r / c)) = r ^ c / ((c.factorial : ℝ) * (1 - ρ)) := by
    rw [hρ]
  unfold erlangC
  rw [hT]
  generalize hS : ∑ n ∈ Finset.range c, r ^ n / (n.factorial : ℝ) = S
  have hS0 : 0 ≤ S := by rw [← hS]; positivity
  have hsumS : ∑ n ∈ Finset.range c, p n = S * p 0 := by
    rw [← hS, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mem_range] at hn
    exact hlow n hn.le
  generalize hTT : r ^ c / ((c.factorial : ℝ) * (1 - ρ)) = T
  have hTpos : 0 < T := by rw [← hTT]; positivity
  have hTp : r ^ c * p 0 / ((c.factorial : ℝ) * (1 - ρ)) = T * p 0 := by
    rw [← hTT]; ring
  rw [hTp, hsumS] at hsum
  have hp0 : p 0 = 1 / (T + S) := by
    field_simp; linarith
  rw [hsumS, hp0]
  field_simp
  ring


lemma qf_loss_Z_pos (x : ℝ) (hx : 0 ≤ x) (c : ℕ) :
    0 < ∑ i ∈ Finset.range (c + 1), x ^ i / (i.factorial : ℝ) := by
  have h0 : (0 : ℕ) ∈ Finset.range (c + 1) := by simp
  have := Finset.single_le_sum (f := fun i : ℕ => x ^ i / (i.factorial : ℝ))
    (fun i _ => by positivity) h0
  simp at this
  linarith

lemma qf_loss_char (lam mu : ℝ) (c : ℕ) (hlam : 0 < lam) (hmu : 0 < mu) (hc : 1 ≤ c)
    (p : ℕ → ℝ) :
    IsSteadyState (truncArrival lam c) (mmcDeath mu c) p ↔
        ((∀ n : ℕ, n ≤ c → p n = ((lam / mu) ^ n / (n.factorial : ℝ)) /
            ∑ i ∈ Finset.range (c + 1), (lam / mu) ^ i / (i.factorial : ℝ)) ∧
          ∀ n : ℕ, c < n → p n = 0) := by
  have hx : 0 ≤ lam / mu := by positivity
  have hZ := qf_loss_Z_pos (lam / mu) hx c
  generalize hZdef : ∑ i ∈ Finset.range (c + 1), (lam / mu) ^ i / (i.factorial : ℝ) = Z at hZ ⊢
  have hr' : lam = (lam / mu) * mu := by field_simp
  have hmu' : mu ≠ 0 := hmu.ne'
  have hcpos : (0 : ℝ) < c := by exact_mod_cast hc
  constructor
  · rintro ⟨hnn, hsum, hbal⟩
    have hd := qf_detailed_of_balanced hbal
    have hlow := qf_mmc_low (lam := lam) (c := c) (p := p) hmu hr' (fun n hn => by
      have := hd n; simpa [truncArrival, hn] using this) 
    have hhigh : ∀ n, c < n → p n = 0 := by
      intro n hn
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have := hd m
      have hm : ¬ m < c := by omega
      have hmin : min (m + 1) c = c := by omega
      simp only [truncArrival, hm, if_false, mmcDeath, hmin, zero_mul] at this
      have hcm : (c : ℝ) * mu ≠ 0 := by positivity
      exact (mul_eq_zero.mp this.symm).resolve_left hcm
    have hs : HasSum p (∑ n ∈ Finset.range (c + 1), p n) := hasSum_sum_of_ne_finset_zero (by
      intro n hn; rw [Finset.mem_range] at hn; exact hhigh n (by omega))
    have h1 := hsum.unique hs
    have hsumZ : ∑ n ∈ Finset.range (c + 1), p n = Z * p 0 := by
      rw [← hZdef, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro n hn; rw [Finset.mem_range] at hn; exact hlow n (by omega)
    rw [hsumZ] at h1
    refine ⟨fun n hn => ?_, hhigh⟩
    rw [hlow n hn]
    field_simp
    linarith
  · rintro ⟨hlow, hhigh⟩
    refine ⟨fun n => ?_, ?_, ?_⟩
    · by_cases hn : n ≤ c
      · rw [hlow n hn]; positivity
      · rw [hhigh n (by omega)]
    · have hs : HasSum p (∑ n ∈ Finset.range (c + 1), p n) := hasSum_sum_of_ne_finset_zero (by
        intro n hn; rw [Finset.mem_range] at hn; exact hhigh n (by omega))
      convert hs using 1
      rw [Finset.sum_congr rfl (fun n hn => hlow n (by rw [Finset.mem_range] at hn; omega)),
        ← Finset.sum_div, hZdef, div_self hZ.ne']
    · apply qf_balanced_of_detailed
      intro n
      by_cases hn : n < c
      · have hmin : min (n + 1) c = n + 1 := by omega
        simp only [truncArrival, hn, if_true, mmcDeath, hmin]
        rw [hlow n hn.le, hlow (n + 1) hn, Nat.factorial_succ, pow_succ]
        push_cast
        field_simp
      · have hmin : min (n + 1) c = c := by omega
        simp only [truncArrival, hn, if_false, zero_mul, mmcDeath, hmin]
        rw [hhigh (n + 1) (by omega), mul_zero]

theorem erlang_loss_formula_core (lam mu : ℝ) (c : ℕ) (r : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (hc : 1 ≤ c) (hr : r = lam / mu) :
    (∃ p : ℕ → ℝ, IsSteadyState (truncArrival lam c) (mmcDeath mu c) p) ∧
      (∀ p : ℕ → ℝ, IsSteadyState (truncArrival lam c) (mmcDeath mu c) p ↔
        ((∀ n : ℕ, n ≤ c → p n = ((lam / mu) ^ n / (n.factorial : ℝ)) /
            ∑ i ∈ Finset.range (c + 1), (lam / mu) ^ i / (i.factorial : ℝ)) ∧
          ∀ n : ℕ, c < n → p n = 0)) ∧
      ∀ p : ℕ → ℝ, IsSteadyState (truncArrival lam c) (mmcDeath mu c) p →
        p c = erlangB c r := by
  refine ⟨?_, qf_loss_char lam mu c hlam hmu hc, ?_⟩
  · refine ⟨fun n => if n ≤ c then ((lam / mu) ^ n / (n.factorial : ℝ)) /
            ∑ i ∈ Finset.range (c + 1), (lam / mu) ^ i / (i.factorial : ℝ) else 0, ?_⟩
    rw [qf_loss_char lam mu c hlam hmu hc]
    refine ⟨fun n hn => by simp [hn], fun n hn => by simp [show ¬ n ≤ c by omega]⟩
  · intro p hp
    rw [(qf_loss_char lam mu c hlam hmu hc p).mp hp |>.1 c le_rfl, erlangB, hr]

end QueueingFundamentals.BirthDeath

open QueueingFundamentals.BirthDeath


theorem solution (lam mu : ℝ) (c : ℕ) (r : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (hc : 1 ≤ c) (hr : r = lam / mu) :
    (∃ p : ℕ → ℝ, IsSteadyState (truncArrival lam c) (mmcDeath mu c) p) ∧
      (∀ p : ℕ → ℝ, IsSteadyState (truncArrival lam c) (mmcDeath mu c) p ↔
        ((∀ n : ℕ, n ≤ c → p n = ((lam / mu) ^ n / (n.factorial : ℝ)) /
            ∑ i ∈ Finset.range (c + 1), (lam / mu) ^ i / (i.factorial : ℝ)) ∧
          ∀ n : ℕ, c < n → p n = 0)) ∧
      ∀ p : ℕ → ℝ, IsSteadyState (truncArrival lam c) (mmcDeath mu c) p →
        p c = erlangB c r := by
  exact erlang_loss_formula_core lam mu c r hlam hmu hc hr
