-- Prove2me | solution 1 for RegLearnGames.FirstOrder.eq_22
-- status  : ACCEPTED   (prove)
-- author  : @suzukasan
-- created : 2026-10-21T10:27:04.354133+00:00
-- url     : https://prove2.me/submissions/1c666145-fbd0-404d-bc7e-c3393354616e

import Mathlib
import Definitions.Def_RegLearnGames_FirstOrder_Setting
import Theorems.Thm_RegLearnGames_FirstOrder_social_cost_eq_sum_inner

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
    (w : ℕ → Fin n → Fin d → ℝ) (T : ℕ)
    (hw : ∀ t ∈ Finset.Icc 1 T, AGT.IsMixedProfile (w t))
    (A₁ A₂ : ℝ) (hA₁ : 0 ≤ A₁)
    (hreg : HasFirstOrderRegret c w T A₁ A₂)
    (sstar : Fin n → Fin d) :
    (∑ t ∈ Finset.Icc 1 T, socialCost c (w t)) ≤
      (∑ t ∈ Finset.Icc 1 T, ∑ i, costVec c (w t) i (sstar i)) +
        A₁ * Real.sqrt ((n : ℝ) * Real.log (d : ℝ)) *
          Real.sqrt (∑ t ∈ Finset.Icc 1 T,
            ∑ i, costVec c (w t) i (sstar i)) +
        A₂ * (n : ℝ) * Real.log (d : ℝ) := by
  classical
  let L : Fin n → ℝ := fun i => ∑ t ∈ Icc 1 T, costVec c (w t) i (sstar i)
  have hL : ∀ i, 0 ≤ L i := fun i =>
    sum_nonneg fun t ht => cost_nonnegative c hc (w t) (hw t ht) i (sstar i)
  have hd : (1 : ℝ) ≤ d := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hl : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg hd
  have hcs : (∑ i, Real.sqrt (Real.log (d : ℝ) * L i)) ≤
      Real.sqrt ((n : ℝ) * Real.log (d : ℝ)) * Real.sqrt (∑ i, L i) := by
    have h := Real.sum_sqrt_mul_sqrt_le (s := (univ : Finset (Fin n)))
      (f := fun _ => Real.log (d : ℝ)) (g := L) (fun _ => hl) hL
    simpa only [← Real.sqrt_mul hl, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] using h
  have hmul := mul_le_mul_of_nonneg_left hcs hA₁
  have hsum := sum_le_sum fun i (_ : i ∈ (univ : Finset (Fin n))) => hreg i (sstar i)
  rw [sum_sub_distrib, sum_add_distrib, ← mul_sum] at hsum
  have hcost : (∑ i, ∑ t ∈ Icc 1 T, (w t i) ⬝ᵥ costVec c (w t) i) =
      ∑ t ∈ Icc 1 T, socialCost c (w t) := by
    rw [sum_comm]
    exact (social_cost_eq_sum_inner c w T hw).symm
  rw [hcost] at hsum
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hLsum : (∑ i, L i) = ∑ t ∈ Icc 1 T, ∑ i, costVec c (w t) i (sstar i) := by
    dsimp [L]
    rw [sum_comm]
  rw [← hLsum]
  change (∑ t ∈ Icc 1 T, socialCost c (w t)) - ∑ i, L i ≤
    A₁ * ∑ i, Real.sqrt (Real.log (d : ℝ) * L i) + (n : ℝ) * (A₂ * Real.log (d : ℝ)) at hsum
  nlinarith
