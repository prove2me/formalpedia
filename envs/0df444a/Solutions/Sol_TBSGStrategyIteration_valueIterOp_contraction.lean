-- Prove2me | solution 1 for TBSGStrategyIteration.valueIterOp_contraction
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T03:18:19.208557+00:00
-- url     : https://prove2.me/submissions/42e1c819-ccb3-4afe-b1d1-c29742072d03

import Mathlib
import Definitions.Def_TBSGStrategyIteration_valueIterOp

namespace Aux_TBSGW31

lemma inf_le {A : Type*} (s : Finset A) (hs : s.Nonempty) (f g : A → ℝ) (D : ℝ)
    (h : ∀ a, f a ≤ g a + D) : s.inf' hs f ≤ s.inf' hs g + D := by
  have : s.inf' hs f - D ≤ s.inf' hs g := Finset.le_inf' _ _ (fun b hb => by
    have := Finset.inf'_le f hb; linarith [h b])
  linarith

lemma sup_le {A : Type*} (s : Finset A) (hs : s.Nonempty) (f g : A → ℝ) (D : ℝ)
    (h : ∀ a, f a ≤ g a + D) : s.sup' hs f ≤ s.sup' hs g + D := by
  have : s.sup' hs f ≤ s.sup' hs g + D := Finset.sup'_le _ _ (fun b hb => by
    have := Finset.le_sup' g hb; linarith [h b])
  exact this

end Aux_TBSGW31

open TBSGStrategyIteration in
theorem solution {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (G : Game S A) (u v : S → ℝ) :
    ‖valueIterOp G u - valueIterOp G v‖ ≤ G.γ * ‖u - v‖ := by
  have hγ := G.γ_pos
  have hD : 0 ≤ G.γ * ‖u - v‖ := mul_nonneg hγ.le (norm_nonneg _)
  have hq : ∀ (x y : S → ℝ) (a : A), qValue G x a ≤ qValue G y a + G.γ * ‖x - y‖ := by
    intro x y a
    unfold qValue
    have h1 : ∑ j, G.P a j * x j - ∑ j, G.P a j * y j ≤ ‖x - y‖ := by
      rw [← Finset.sum_sub_distrib]
      calc ∑ j, (G.P a j * x j - G.P a j * y j) ≤ ∑ j, G.P a j * ‖x - y‖ := by
            apply Finset.sum_le_sum
            intro j _
            have hj : x j - y j ≤ ‖x - y‖ := by
              have := norm_le_pi_norm (x - y) j
              rw [Pi.sub_apply, Real.norm_eq_abs] at this
              exact le_trans (le_abs_self _) this
            rw [← mul_sub]
            exact mul_le_mul_of_nonneg_left hj (G.P_nonneg a j)
        _ = ‖x - y‖ := by rw [← Finset.sum_mul, G.P_sum_one, one_mul]
    nlinarith [mul_le_mul_of_nonneg_left h1 hγ.le]
  have hsym : ‖v - u‖ = ‖u - v‖ := norm_sub_rev v u
  rw [pi_norm_le_iff_of_nonneg hD]
  intro i
  rw [Pi.sub_apply, Real.norm_eq_abs, abs_le]
  unfold valueIterOp
  split_ifs
  · have h1 := Aux_TBSGW31.inf_le (actionSet G i) (actionSet_nonempty G i) _ _ _ (hq u v)
    have h2 := Aux_TBSGW31.inf_le (actionSet G i) (actionSet_nonempty G i) _ _ _ (hq v u)
    rw [hsym] at h2
    constructor <;> linarith
  · have h1 := Aux_TBSGW31.sup_le (actionSet G i) (actionSet_nonempty G i) _ _ _ (hq u v)
    have h2 := Aux_TBSGW31.sup_le (actionSet G i) (actionSet_nonempty G i) _ _ _ (hq v u)
    rw [hsym] at h2
    constructor <;> linarith
