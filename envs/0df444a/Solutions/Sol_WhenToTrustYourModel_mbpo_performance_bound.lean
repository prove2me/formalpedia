-- Prove2me | solution 1 for WhenToTrustYourModel.mbpo_performance_bound
-- status  : ACCEPTED   (prove)
-- author  : @ytako6706
-- created : 2026-11-25T09:52:41.888557+00:00
-- url     : https://prove2.me/submissions/140b32b1-670a-4612-8d68-c190a52a02ab

import Mathlib
import Definitions.Def_WhenToTrustYourModel_Basic

open Finset
open WhenToTrustYourModel

namespace MBPOAux

variable {S A : Type*} [Fintype S] [Fintype A]

lemma stateDist_succ (ρ0 : S → ℝ) (π : S → A → ℝ) (P : S → A → S → ℝ) (t : ℕ) (s' : S) :
    stateDist ρ0 (fun _ => π) (fun _ => P) (t + 1) s' =
      ∑ s, stateDist ρ0 (fun _ => π) (fun _ => P) t s * ∑ a, π s a * P s a s' := rfl

lemma stateDist_isDist (ρ0 : S → ℝ) (hρ0 : IsDist ρ0) (π : S → A → ℝ) (hπ : IsPolicy π)
    (P : S → A → S → ℝ) (hP : IsDynamics P) (t : ℕ) :
    IsDist (stateDist ρ0 (fun _ => π) (fun _ => P) t) := by
  induction t with
  | zero => exact hρ0
  | succ t ih =>
    refine ⟨fun s' => ?_, ?_⟩
    · rw [stateDist_succ]
      exact sum_nonneg fun s _ => mul_nonneg (ih.1 s)
        (sum_nonneg fun a _ => mul_nonneg ((hπ s).1 a) ((hP s a).1 s'))
    · simp_rw [stateDist_succ, mul_sum]
      rw [sum_comm]
      calc ∑ s, ∑ s', ∑ a, stateDist ρ0 (fun _ => π) (fun _ => P) t s * (π s a * P s a s')
          = ∑ s, stateDist ρ0 (fun _ => π) (fun _ => P) t s * ∑ a, π s a * ∑ s', P s a s' := by
            refine sum_congr rfl fun s _ => ?_
            rw [sum_comm, mul_sum]
            refine sum_congr rfl fun a _ => ?_
            rw [mul_sum, mul_sum]
        _ = 1 := by
            simp_rw [fun s a => (hP s a).2, mul_one, fun s => (hπ s).2, mul_one]
            exact ih.2

/-- One step of the `ℓ¹` coupling estimate between two state marginals. -/
lemma l1_step (dA dB : S → ℝ) (hdA : ∀ s, 0 ≤ dA s) (π1 π2 : S → A → ℝ)
    (hπ1 : ∀ s a, 0 ≤ π1 s a) (hπ2 : IsPolicy π2) (P1 P2 : S → A → S → ℝ)
    (hP2 : IsDynamics P2) :
    ∑ s', |∑ s, dA s * ∑ a, π1 s a * P1 s a s' - ∑ s, dB s * ∑ a, π2 s a * P2 s a s'| ≤
      ∑ s, |dA s - dB s| + ∑ s, dA s * (∑ a, π1 s a * ∑ s', |P1 s a s' - P2 s a s'|) +
        ∑ s, dA s * ∑ a, |π1 s a - π2 s a| := by
  have hpt : ∀ s', |∑ s, dA s * ∑ a, π1 s a * P1 s a s' - ∑ s, dB s * ∑ a, π2 s a * P2 s a s'|
      ≤ ∑ s, ∑ a, (|dA s - dB s| * π2 s a * P2 s a s' +
          dA s * π1 s a * |P1 s a s' - P2 s a s'| + dA s * |π1 s a - π2 s a| * P2 s a s') := by
    intro s'
    have heq : ∑ s, dA s * ∑ a, π1 s a * P1 s a s' - ∑ s, dB s * ∑ a, π2 s a * P2 s a s' =
        ∑ s, ∑ a, ((dA s - dB s) * π2 s a * P2 s a s' +
          dA s * π1 s a * (P1 s a s' - P2 s a s') + dA s * (π1 s a - π2 s a) * P2 s a s') := by
      rw [← sum_sub_distrib]
      refine sum_congr rfl fun s _ => ?_
      rw [mul_sum, mul_sum, ← sum_sub_distrib]
      exact sum_congr rfl fun a _ => by ring
    rw [heq]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun s _ => ?_)
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun a _ => ?_)
    have h1 := (hπ2 s).1 a
    have h2 := (hP2 s a).1 s'
    have h3 := hdA s
    have h4 := hπ1 s a
    refine (abs_add_le _ _).trans ?_
    refine add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_
    · rw [abs_mul, abs_mul, abs_of_nonneg h1, abs_of_nonneg h2]
    · rw [abs_mul, abs_mul, abs_of_nonneg h3, abs_of_nonneg h4]
    · rw [abs_mul, abs_mul, abs_of_nonneg h3, abs_of_nonneg h2]
  refine (sum_le_sum fun s' _ => hpt s').trans (le_of_eq ?_)
  rw [← sum_add_distrib, ← sum_add_distrib, sum_comm]
  refine sum_congr rfl fun s _ => ?_
  rw [sum_comm]
  conv_rhs => rw [← mul_one |dA s - dB s|, ← (hπ2 s).2, mul_sum, mul_sum, mul_sum,
    ← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun a _ => ?_
  rw [sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, ← mul_sum, (hP2 s a).2]
  ring

end MBPOAux

open MBPOAux

theorem solution {S A : Type*} [Fintype S] [Fintype A]
    (γ : ℝ) (hγ₀ : 0 < γ) (hγ₁ : γ < 1)
    (r : S → A → ℝ) (rmax : ℝ) (hr : ∀ s a, |r s a| ≤ rmax)
    (ρ₀ : S → ℝ) (hρ₀ : IsDist ρ₀)
    (π πD : S → A → ℝ) (hπ : IsPolicy π) (hπD : IsPolicy πD)
    (P Phat : S → A → S → ℝ) (hP : IsDynamics P) (hPhat : IsDynamics Phat)
    (εm επ : ℝ)
    (hm : ∀ t, expectedTV (stateDist ρ₀ (fun _ => πD) (fun _ => P) t) πD P Phat ≤ εm)
    (hdiv : ∀ s, tvDist (πD s) (π s) ≤ επ) :
    policyReturn γ r ρ₀ π Phat
        - (2 * γ * rmax * (εm + 2 * επ) / (1 - γ) ^ 2 + 4 * rmax * επ / (1 - γ)) ≤
      policyReturn γ r ρ₀ π P := by
  classical
  -- nonemptiness, `rmax ≥ 0`, `επ ≥ 0`
  obtain ⟨s0, -, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := univ) (f := ρ₀)
    (by rw [hρ₀.2]; norm_num)
  obtain ⟨a0, -, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := univ) (f := π s0)
    (by rw [(hπ s0).2]; norm_num)
  have hrmax : 0 ≤ rmax := (abs_nonneg _).trans (hr s0 a0)
  have hεπ : 0 ≤ επ := by
    refine le_trans ?_ (hdiv s0)
    unfold tvDist
    exact mul_nonneg (by norm_num) (sum_nonneg fun _ _ => abs_nonneg _)
  set dD := stateDist ρ₀ (fun _ => πD) (fun _ => P) with hdD
  set dH := stateDist ρ₀ (fun _ => π) (fun _ => Phat) with hdH
  set d1 := stateDist ρ₀ (fun _ => π) (fun _ => P) with hd1
  have hDd := stateDist_isDist ρ₀ hρ₀ πD hπD P hP
  have hHd := stateDist_isDist ρ₀ hρ₀ π hπ Phat hPhat
  have h1d := stateDist_isDist ρ₀ hρ₀ π hπ P hP
  -- policy-divergence term
  have hdivsum : ∀ t, ∑ s, dD t s * ∑ a, |πD s a - π s a| ≤ 2 * επ := by
    intro t
    calc ∑ s, dD t s * ∑ a, |πD s a - π s a| ≤ ∑ s, dD t s * (2 * επ) := by
          refine sum_le_sum fun s _ => mul_le_mul_of_nonneg_left ?_ ((hDd t).1 s)
          have := hdiv s
          unfold tvDist at this
          linarith
      _ = 2 * επ := by rw [← sum_mul, (hDd t).2, one_mul]
  -- marginal gap between the data process and the model process
  have hE : ∀ t : ℕ, ∑ s, |dD t s - dH t s| ≤ t * (2 * εm + 2 * επ) := by
    intro t
    induction t with
    | zero => simp [hdD, hdH, stateDist, chainDist]
    | succ t ih =>
      simp_rw [hdD, hdH, stateDist_succ]
      refine (l1_step _ _ (hDd t).1 πD π (fun s a => (hπD s).1 a) hπ P Phat hPhat).trans ?_
      have hmt : ∑ s, dD t s * (∑ a, πD s a * ∑ s', |P s a s' - Phat s a s'|) =
          2 * expectedTV (dD t) πD P Phat := by
        simp only [expectedTV, tvDist, mul_sum]
        exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
      have := hm t
      have := hdivsum t
      rw [← hdD, ← hdH]
      rw [hmt]
      push_cast
      nlinarith
  -- marginal gap between the data process and the true process under `π`
  have hF : ∀ t : ℕ, ∑ s, |dD t s - d1 t s| ≤ t * (2 * επ) := by
    intro t
    induction t with
    | zero => simp [hdD, hd1, stateDist, chainDist]
    | succ t ih =>
      simp_rw [hdD, hd1, stateDist_succ]
      refine (l1_step _ _ (hDd t).1 πD π (fun s a => (hπD s).1 a) hπ P P hP).trans ?_
      have := hdivsum t
      rw [← hdD, ← hd1]
      simp only [sub_self, abs_zero, sum_const_zero, mul_zero, add_zero]
      push_cast
      nlinarith
  -- per-step reward gap
  have hexp : ∀ (d : ℕ → S → ℝ) (Q : S → A → S → ℝ), d = stateDist ρ₀ (fun _ => π) (fun _ => Q) →
      ∀ t, WhenToTrustYourModel.expReward r ρ₀ (fun _ => π) (fun _ => Q) t =
        ∑ s, ∑ a, d t s * π s a * r s a := by
    intro d Q hd t; subst hd; rfl
  have hgap : ∀ t : ℕ, WhenToTrustYourModel.expReward r ρ₀ (fun _ => π) (fun _ => Phat) t -
      WhenToTrustYourModel.expReward r ρ₀ (fun _ => π) (fun _ => P) t ≤
        t * (rmax * (2 * εm + 4 * επ)) := by
    intro t
    rw [hexp dH Phat hdH, hexp d1 P hd1, ← sum_sub_distrib]
    calc ∑ s, (∑ a, dH t s * π s a * r s a - ∑ a, d1 t s * π s a * r s a)
        ≤ ∑ s, |dH t s - d1 t s| * rmax := by
          refine sum_le_sum fun s _ => ?_
          rw [← sum_sub_distrib]
          calc ∑ a, (dH t s * π s a * r s a - d1 t s * π s a * r s a)
              = (dH t s - d1 t s) * ∑ a, π s a * r s a := by
                rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
            _ ≤ |dH t s - d1 t s| * |∑ a, π s a * r s a| := by
                rw [← abs_mul]; exact le_abs_self _
            _ ≤ |dH t s - d1 t s| * rmax := by
                refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
                refine (abs_sum_le_sum_abs _ _).trans ?_
                calc ∑ a, |π s a * r s a| ≤ ∑ a, π s a * rmax := by
                      refine sum_le_sum fun a _ => ?_
                      rw [abs_mul, abs_of_nonneg ((hπ s).1 a)]
                      exact mul_le_mul_of_nonneg_left (hr s a) ((hπ s).1 a)
                  _ = rmax := by rw [← sum_mul, (hπ s).2, one_mul]
      _ ≤ ∑ s, (|dD t s - dH t s| + |dD t s - d1 t s|) * rmax := by
          refine sum_le_sum fun s _ => mul_le_mul_of_nonneg_right ?_ hrmax
          calc |dH t s - d1 t s| = |(dD t s - d1 t s) - (dD t s - dH t s)| := by ring_nf
            _ ≤ |dD t s - d1 t s| + |dD t s - dH t s| := abs_sub _ _
            _ = _ := add_comm _ _
      _ = (∑ s, |dD t s - dH t s| + ∑ s, |dD t s - d1 t s|) * rmax := by
          rw [← sum_add_distrib, sum_mul]
      _ ≤ (t * (2 * εm + 2 * επ) + t * (2 * επ)) * rmax :=
          mul_le_mul_of_nonneg_right (add_le_add (hE t) (hF t)) hrmax
      _ = t * (rmax * (2 * εm + 4 * επ)) := by ring
  -- bounded rewards give summability
  have hbdd : ∀ (Q : S → A → S → ℝ), IsDynamics Q → ∀ t,
      |WhenToTrustYourModel.expReward r ρ₀ (fun _ => π) (fun _ => Q) t| ≤ rmax := by
    intro Q hQ t
    have hQd := stateDist_isDist ρ₀ hρ₀ π hπ Q hQ t
    rw [hexp _ Q rfl]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ s, |∑ a, stateDist ρ₀ (fun _ => π) (fun _ => Q) t s * π s a * r s a|
        ≤ ∑ s, stateDist ρ₀ (fun _ => π) (fun _ => Q) t s * rmax := by
          refine sum_le_sum fun s _ => (abs_sum_le_sum_abs _ _).trans ?_
          calc ∑ a, |stateDist ρ₀ (fun _ => π) (fun _ => Q) t s * π s a * r s a|
              ≤ ∑ a, stateDist ρ₀ (fun _ => π) (fun _ => Q) t s * π s a * rmax := by
                refine sum_le_sum fun a _ => ?_
                rw [abs_mul, abs_mul, abs_of_nonneg (hQd.1 s), abs_of_nonneg ((hπ s).1 a)]
                exact mul_le_mul_of_nonneg_left (hr s a)
                  (mul_nonneg (hQd.1 s) ((hπ s).1 a))
            _ = stateDist ρ₀ (fun _ => π) (fun _ => Q) t s * rmax := by
                rw [← sum_mul, ← mul_sum, (hπ s).2, mul_one]
      _ = rmax := by rw [← sum_mul, hQd.2, one_mul]
  have hsum : ∀ (Q : S → A → S → ℝ), IsDynamics Q →
      Summable (fun t : ℕ => γ ^ t *
        WhenToTrustYourModel.expReward r ρ₀ (fun _ => π) (fun _ => Q) t) := by
    intro Q hQ
    refine Summable.of_norm_bounded
      ((summable_geometric_of_lt_one hγ₀.le hγ₁).mul_left rmax) fun t => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hγ₀.le t), mul_comm rmax]
    exact mul_le_mul_of_nonneg_left (hbdd Q hQ t) (pow_nonneg hγ₀.le t)
  have hγn : ‖γ‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hγ₀]; exact hγ₁
  have hgeo : Summable (fun t : ℕ => (t : ℝ) * γ ^ t) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hγn).summable
  have hmain : policyReturn γ r ρ₀ π Phat - policyReturn γ r ρ₀ π P ≤
      rmax * (2 * εm + 4 * επ) * (γ / (1 - γ) ^ 2) := by
    unfold policyReturn discReturn
    rw [← (hsum Phat hPhat).tsum_sub (hsum P hP), ← tsum_coe_mul_geometric_of_norm_lt_one hγn,
      ← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun t => ?_) ((hsum Phat hPhat).sub (hsum P hP))
      (hgeo.mul_left _)
    rw [← mul_sub]
    calc γ ^ t * (WhenToTrustYourModel.expReward r ρ₀ (fun _ => π) (fun _ => Phat) t -
          WhenToTrustYourModel.expReward r ρ₀ (fun _ => π) (fun _ => P) t)
        ≤ γ ^ t * (t * (rmax * (2 * εm + 4 * επ))) :=
          mul_le_mul_of_nonneg_left (hgap t) (pow_nonneg hγ₀.le t)
      _ = _ := by ring
  have h1g : 0 < 1 - γ := by linarith
  have hextra : 0 ≤ 4 * rmax * επ / (1 - γ) := by positivity
  have heq : rmax * (2 * εm + 4 * επ) * (γ / (1 - γ) ^ 2) =
      2 * γ * rmax * (εm + 2 * επ) / (1 - γ) ^ 2 := by
    field_simp; ring
  linarith
