-- Prove2me | solution 1 for RegLearnGames.FirstOrder.quadratic_inequality
-- status  : ACCEPTED   (prove)
-- author  : @suzukasan
-- created : 2026-10-21T10:27:33.729732+00:00
-- url     : https://prove2.me/submissions/9c8880b2-d97f-456d-aace-c7c3fec26f0a

import Mathlib
import Definitions.Def_RegLearnGames_FirstOrder_Setting
import Theorems.Thm_RegLearnGames_FirstOrder_eq_22
import Theorems.Thm_RegLearnGames_FirstOrder_smoothness_step

open Finset RegLearnGames.FirstOrder

private lemma cost_nonnegative {n d : ℕ} (c : Fin n → (Fin n → Fin d) → ℝ)
    (hc : ∀ i s, c i s ∈ Set.Icc (0 : ℝ) 1)
    (w : Fin n → Fin d → ℝ) (hw : AGT.IsMixedProfile w) (i : Fin n) (x : Fin d) :
    0 ≤ costVec c w i x := by
  classical
  unfold costVec AGT.expectedPayoff AGT.profileProb
  refine sum_nonneg fun s _ => mul_nonneg ?_ (hc i s).1
  refine prod_nonneg fun j _ => ?_
  by_cases hj : j = i
  · subst j
    simp only [Function.update_self, Pi.single_apply]
    split_ifs <;> norm_num
  · rw [Function.update_of_ne hj]
    exact (hw j).1 _

theorem solution {n d : ℕ} [NeZero d]
    (c : Fin n → (Fin n → Fin d) → ℝ)
    (hc : ∀ i s, c i s ∈ Set.Icc (0 : ℝ) 1)
    (lam mu : ℝ) (hmu₀ : 0 < mu) (hmu₁ : mu < 1)
    (hsmooth : IsSmoothCost c lam mu)
    (A₁ A₂ : ℝ) (hA₁ : 0 ≤ A₁)
    (T : ℕ) (hT : 1 ≤ T)
    (w : ℕ → Fin n → Fin d → ℝ)
    (hw : ∀ t ∈ Finset.Icc 1 T, AGT.IsMixedProfile (w t))
    (hreg : HasFirstOrderRegret c w T A₁ A₂) :
    let x : ℝ := Real.sqrt (lam * (T : ℝ) * optCost c +
      mu * (∑ t ∈ Finset.Icc 1 T, socialCost c (w t)))
    (1 / mu) * (x ^ 2 - lam * (T : ℝ) * optCost c) ≤
      x ^ 2 + A₁ * Real.sqrt ((n : ℝ) * Real.log (d : ℝ)) * x +
        A₂ * (n : ℝ) * Real.log (d : ℝ) := by
  classical
  obtain ⟨sstar, hsstar⟩ := hsmooth
  let S : ℝ := ∑ t ∈ Icc 1 T, socialCost c (w t)
  let D : ℝ := ∑ t ∈ Icc 1 T, ∑ i, costVec c (w t) i (sstar i)
  let Y : ℝ := lam * (T : ℝ) * optCost c + mu * S
  have hD : 0 ≤ D := sum_nonneg fun t ht => sum_nonneg fun i _ =>
    cost_nonnegative c hc (w t) (hw t ht) i (sstar i)
  have hDY : D ≤ Y := by
    calc
      D ≤ ∑ t ∈ Icc 1 T, (lam * optCost c + mu * socialCost c (w t)) :=
        sum_le_sum fun t ht => smoothness_step c (w t) (hw t ht) lam mu sstar hsstar
      _ = Y := by
        simp only [sum_add_distrib, sum_const, ← mul_sum, Nat.card_Icc, Nat.add_sub_cancel,
          nsmul_eq_mul]
        dsimp [Y, S]
        ring
  have hY : 0 ≤ Y := hD.trans hDY
  have hx : (Real.sqrt Y) ^ 2 = Y := Real.sq_sqrt hY
  have heq := eq_22 c hc w T hw A₁ A₂ hA₁ hreg sstar
  change S ≤ D + A₁ * Real.sqrt ((n : ℝ) * Real.log (d : ℝ)) * Real.sqrt D +
    A₂ * (n : ℝ) * Real.log (d : ℝ) at heq
  have hmono := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hDY)
    (mul_nonneg hA₁ (Real.sqrt_nonneg ((n : ℝ) * Real.log (d : ℝ))))
  have hbound : S ≤ Y + A₁ * Real.sqrt ((n : ℝ) * Real.log (d : ℝ)) * Real.sqrt Y +
      A₂ * (n : ℝ) * Real.log (d : ℝ) := by linarith
  have hcancel : (1 / mu) * (Y - lam * (T : ℝ) * optCost c) = S := by
    dsimp [Y]
    field_simp [hmu₀.ne'] <;> ring
  change (1 / mu) * ((Real.sqrt Y) ^ 2 - lam * (T : ℝ) * optCost c) ≤
    (Real.sqrt Y) ^ 2 + A₁ * Real.sqrt ((n : ℝ) * Real.log (d : ℝ)) * Real.sqrt Y +
      A₂ * (n : ℝ) * Real.log (d : ℝ)
  rw [hx, hcancel]
  exact hbound
