-- Prove2me | solution 1 for QueueingFundamentals.BirthDeath.mminf_steady_state
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T17:14:57.965868+00:00
-- url     : https://prove2.me/submissions/2dc05be6-b963-4eca-bd54-fb948c2a32cf

import Mathlib
import Definitions.Def_QueueingFundamentals_BirthDeath_Balance

namespace MMInfAux

open QueueingFundamentals.BirthDeath

theorem exp_hasSum (r : ℝ) : HasSum (fun n : ℕ => r ^ n / (n.factorial : ℝ)) (Real.exp r) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp r

/-- detailed balance implies global balance -/
theorem balanced_of_detailed (lam mu : ℝ) (p : ℕ → ℝ)
    (h : ∀ n : ℕ, lam * p n = ((n : ℝ) + 1) * mu * p (n + 1)) :
    IsBalanced (fun _ => lam) (infDeath mu) p := by
  refine ⟨?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have h1 := h m
    have h2 := h (m + 1)
    simp only [infDeath, Nat.add_sub_cancel]
    push_cast at h1 h2 ⊢
    linarith
  · have := h 0
    simp only [infDeath]
    push_cast at this ⊢
    linarith

/-- global balance implies detailed balance -/
theorem detailed_of_balanced (lam mu : ℝ) (p : ℕ → ℝ)
    (h : IsBalanced (fun _ => lam) (infDeath mu) p) :
    ∀ n : ℕ, lam * p n = ((n : ℝ) + 1) * mu * p (n + 1) := by
  obtain ⟨hb, h0⟩ := h
  intro n
  induction n with
  | zero => simp only [infDeath] at h0; push_cast at h0 ⊢; linarith
  | succ m ih =>
    have := hb (m + 1) (by omega)
    simp only [infDeath, Nat.add_sub_cancel] at this
    push_cast at this ⊢
    linarith

theorem poisson_detailed (lam mu r : ℝ) (hmu : 0 < mu) (hr : r = lam / mu) (c : ℝ) (n : ℕ) :
    lam * (c * (r ^ n / (n.factorial : ℝ))) =
      ((n : ℝ) + 1) * mu * (c * (r ^ (n + 1) / ((n + 1).factorial : ℝ))) := by
  have hm : mu ≠ 0 := hmu.ne'
  have hl : lam = r * mu := by rw [hr]; field_simp
  rw [hl, Nat.factorial_succ]
  push_cast
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

end MMInfAux

open QueueingFundamentals.BirthDeath in
theorem solution (lam mu r : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (hr : r = lam / mu) :
    (∃ p : ℕ → ℝ, IsSteadyState (fun _ => lam) (infDeath mu) p) ∧
      ∀ p : ℕ → ℝ, IsSteadyState (fun _ => lam) (infDeath mu) p ↔
        ∀ n : ℕ, p n = r ^ n * Real.exp (-r) / (n.factorial : ℝ) := by
  have hrpos : 0 < r := by rw [hr]; positivity
  have key : ∀ p : ℕ → ℝ, (∀ n : ℕ, p n = r ^ n * Real.exp (-r) / (n.factorial : ℝ)) →
      IsSteadyState (fun _ => lam) (infDeath mu) p := by
    intro p hp
    have hp' : ∀ n, p n = Real.exp (-r) * (r ^ n / (n.factorial : ℝ)) := by
      intro n; rw [hp n]; ring
    refine ⟨?_, ?_, ?_⟩
    · intro n; rw [hp n]; positivity
    · have := (MMInfAux.exp_hasSum r).mul_left (Real.exp (-r))
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at this
      have e : (fun i : ℕ => Real.exp (-r) * (r ^ i / (i.factorial : ℝ))) = p := by
        funext n; exact (hp' n).symm
      rwa [e] at this
    · apply MMInfAux.balanced_of_detailed
      intro n
      rw [hp' n, hp' (n + 1)]
      exact MMInfAux.poisson_detailed lam mu r hmu hr _ n
  refine ⟨⟨_, key _ (fun n => rfl)⟩, fun p => ⟨fun hp => ?_, key p⟩⟩
  obtain ⟨_, hsum, hbal⟩ := hp
  have hd := MMInfAux.detailed_of_balanced lam mu p hbal
  have hform : ∀ n, p n = p 0 * (r ^ n / (n.factorial : ℝ)) := by
    intro n
    induction n with
    | zero => simp
    | succ m ih =>
      have h1 := hd m
      have h2 := MMInfAux.poisson_detailed lam mu r hmu hr (p 0) m
      have hne : ((m : ℝ) + 1) * mu ≠ 0 := by positivity
      rw [← ih] at h2
      have := h1.symm.trans h2
      exact mul_left_cancel₀ hne this
  have hs2 := (MMInfAux.exp_hasSum r).mul_left (p 0)
  have heq : (fun n => p 0 * (r ^ n / (n.factorial : ℝ))) = p := by
    funext n; exact (hform n).symm
  rw [heq] at hs2
  have hp0 : p 0 * Real.exp r = 1 := hsum.unique hs2 |>.symm
  have hp0' : p 0 = Real.exp (-r) := by
    rw [Real.exp_neg]; field_simp; linarith
  intro n
  rw [hform n, hp0']
  ring
