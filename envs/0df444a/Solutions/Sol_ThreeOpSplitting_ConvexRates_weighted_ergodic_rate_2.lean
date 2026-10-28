-- Prove2me | solution 2 for ThreeOpSplitting.ConvexRates.weighted_ergodic_rate
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-26T16:26:14.582192+00:00
-- url     : https://prove2.me/submissions/52afd14d-a810-4eef-bdbf-6b30cfce9a4f

import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_ThreeOpSplitting_ConvexRates_Algorithm
import Theorems.Thm_ThreeOpSplitting_ConvexRates_fejer_monotone
import Theorems.Thm_ThreeOpSplitting_ConvexRates_gradient_tail_sum
import Theorems.Thm_ThreeOpSplitting_ConvexRates_iterates_in_ball
import Theorems.Thm_ThreeOpSplitting_ConvexRates_one_step_inequality
import Theorems.Thm_ThreeOpSplitting_ConvexRates_weighted_ergodic_distance

import Theorems.Thm_WeightedAverage_gauss_real
import Theorems.Thm_WeightedAverage_telescope_weighted
import Theorems.Thm_WeightedAverage_abel_sum
import Theorems.Thm_ERealFn_exists_real_of_ne_top_ne_bot
import Theorems.Thm_ERealFn_jensen_finite_sum
import Theorems.Thm_ProxOperator_prox_ne_top
set_option autoImplicit false
open InnerProductSpace Filter Topology
open ThreeOpSplitting.ConvexRates

-- carved from submission af8c70db-6fa0-4580-9851-54457c202aeb, lines 865-1092

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f g : H → EReal) (h : H → ℝ) (β γ : ℝ) (hβ : 0 < β) (hγ : 0 < γ) (hγβ : γ < 2 * β)
    (hf : IsProperClosedConvex f) (hg : IsProperClosedConvex g) (hh : IsSmoothConvex β h)
    (proxf proxg : H → H) (hproxf : IsProx γ f proxf) (hproxg : IsProx γ g proxg)
    (z0 zstar : H) (hfix : splittingOp proxf proxg (gradient h) γ zstar = zstar)
    (L : NNReal)
    (hfin : ∀ x ∈ Metric.closedBall (proxg zstar) ((1 + γ / β) * ‖z0 - zstar‖), f x ≠ ⊤)
    (hLip : LipschitzOnWith L (fun x => (f x).toReal)
      (Metric.closedBall (proxg zstar) ((1 + γ / β) * ‖z0 - zstar‖))) :
    objective f g h (proxg zstar) ≠ ⊤ ∧
      ∃ C : ℝ, ∀ k : ℕ,
        objective f g h (weightedErgodic (algXg proxf proxg (gradient h) γ z0) k) ≤
          objective f g h (proxg zstar) + ((C / ((k : ℝ) + 1) : ℝ) : EReal) := by
  set x := proxg zstar with hx
  set r := (1 + γ / β) * ‖z0 - zstar‖ with hr
  have hr0 : 0 ≤ r := by positivity
  have hball := ThreeOpSplitting.ConvexRates.iterates_in_ball f g h β γ hβ hγ hγβ hf hg hh proxf proxg hproxf hproxg z0 zstar hfix
  have hfej := ThreeOpSplitting.ConvexRates.fejer_monotone f g h β γ hβ hγ hγβ hf hg hh proxf proxg hproxf hproxg z0 zstar hfix
  have hwed := ThreeOpSplitting.ConvexRates.weighted_ergodic_distance f g h β γ hβ hγ hγβ hf hg hh proxf proxg hproxf hproxg
    z0 zstar hfix
  set z := algZ proxf proxg (gradient h) γ z0 with hz
  set xg := algXg proxf proxg (gradient h) γ z0 with hxg
  set xf := algXf proxf proxg (gradient h) γ z0 with hxf
  obtain ⟨hfb, _, _, hfconv⟩ := hf
  obtain ⟨hgb, _, _, hgconv⟩ := hg
  have hf' : IsProperClosedConvex f := ⟨hfb, ‹_›, ‹_›, hfconv⟩
  have hg' : IsProperClosedConvex g := ⟨hgb, ‹_›, ‹_›, hgconv⟩
  have fx : f x ≠ ⊤ := hfin x (Metric.mem_closedBall_self hr0)
  have gx : g x ≠ ⊤ := ProxOperator.prox_ne_top γ g proxg hg' hproxg zstar
  have fxf : ∀ k, f (xf k) ≠ ⊤ := fun k => hfin _ (hball k).1
  have gxg : ∀ k, g (xg k) ≠ ⊤ := fun k => ProxOperator.prox_ne_top γ g proxg hg' hproxg (z k)
  have hobj : ∀ y, f y ≠ ⊤ → g y ≠ ⊤ →
      objective f g h y = (((f y).toReal + (g y).toReal + h y : ℝ) : EReal) := by
    intro y h1 h2
    obtain ⟨a, ha⟩ := ERealFn.exists_real_of_ne_top_ne_bot h1 (hfb y)
    obtain ⟨b, hb⟩ := ERealFn.exists_real_of_ne_top_ne_bot h2 (hgb y)
    unfold objective
    rw [ha, hb, EReal.toReal_coe, EReal.toReal_coe, ← EReal.coe_add, ← EReal.coe_add]
  refine ⟨by rw [hobj x fx gx]; exact EReal.coe_ne_top _, ?_⟩
  set Fs := (f x).toReal + (g x).toReal + h x with hFs
  -- constants
  set M1 := ‖z0 - zstar‖ + ‖zstar - x‖ with hM1
  have hzx : ∀ k, ‖z k - x‖ ≤ M1 := by
    intro k
    have h1 : ‖z k - zstar‖ ≤ ‖z0 - zstar‖ := hfej (Nat.zero_le k)
    have h2 := norm_sub_le_norm_sub_add_norm_sub (z k) zstar x
    linarith
  set ε := (γ / (2 * β) + 1) / 2 with hε
  have hε1 : γ / (2 * β) < ε := by
    have : γ / (2 * β) < 1 := by rw [div_lt_one (by positivity)]; linarith
    rw [hε]; linarith
  have hε2 : ε < 1 := by
    have : γ / (2 * β) < 1 := by rw [div_lt_one (by positivity)]; linarith
    rw [hε]; linarith
  obtain ⟨hcsum, _⟩ := ThreeOpSplitting.ConvexRates.gradient_tail_sum f g h β γ hβ hγ hγβ hf' hg' hh proxf proxg hproxf hproxg
    z0 zstar hfix ε hε1 hε2
  set c : ℕ → ℝ := fun i => ‖gradient h (xg i) - gradient h x‖ ^ 2 with hc
  set S := ∑' i, c i with hS
  have hc0 : ∀ i, 0 ≤ c i := fun i => sq_nonneg _
  have hpart : ∀ n, ∑ i ∈ Finset.range n, c i ≤ S := fun n => hcsum.sum_le_tsum _ (fun i _ => hc0 i)
  set gs := gradient h x with hgs
  set Q := M1 ^ 2 + γ ^ 2 * S + 4 * γ * ‖z0 - zstar‖ * ‖gs‖ with hQ
  refine ⟨Q / γ + 5 * L * ‖z0 - zstar‖, fun k => ?_⟩
  -- per-step real inequality
  set a : ℕ → ℝ := fun i => (f (xf i)).toReal with ha
  set b : ℕ → ℝ := fun i => (g (xg i)).toReal with hb
  have efa : ∀ i, f (xf i) = a i := fun i => (EReal.coe_toReal (fxf i) (hfb _)).symm
  have egb : ∀ i, g (xg i) = b i := fun i => (EReal.coe_toReal (gxg i) (hgb _)).symm
  set E : ℕ → ℝ := fun i => a i + b i + h (xg i) - Fs with hE
  have hstep : ∀ i, 2 * γ * E i ≤ ‖z i - x‖ ^ 2 - ‖z (i + 1) - x‖ ^ 2 + γ ^ 2 * c i
      + 2 * γ * ⟪z i - z (i + 1), gs⟫_ℝ := by
    intro i
    have hos := ThreeOpSplitting.ConvexRates.one_step_inequality f g h β γ hβ hγ hγβ hf' hg' hh proxf proxg hproxf hproxg z0
      zstar hfix i
    have hobx := hobj x fx gx
    rw [← hFs] at hobx
    change ((2 * γ : ℝ) : EReal) * (f (xf i) + g (xg i) + ((h (xg i) : ℝ) : EReal)
      - objective f g h x) ≤ _ at hos
    rw [efa, egb, hobx, ← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_sub, ← EReal.coe_mul,
      EReal.coe_le_coe_iff] at hos
    set δ := z i - z (i + 1) with hδ
    set e := gradient h (xg i) - gs with he
    have hsplit : ⟪δ, gradient h (xg i)⟫_ℝ = ⟪δ, e⟫_ℝ + ⟪δ, gs⟫_ℝ := by
      rw [← inner_add_right, he, sub_add_cancel]
    have hsq : 0 ≤ ‖δ - γ • e‖ ^ 2 := sq_nonneg _
    rw [norm_sub_sq_real, norm_smul, real_inner_smul_right, Real.norm_eq_abs, abs_of_pos hγ]
      at hsq
    have hci : c i = ‖e‖ ^ 2 := rfl
    change 2 * γ * (a i + b i + h (xg i) - Fs) ≤ _
    rw [hci]
    nlinarith
  -- weighted sum
  set n := k + 1 with hn
  have hsumE : 2 * γ * ∑ i ∈ Finset.range n, ((i : ℝ) + 1) * E i ≤ (n : ℝ) * Q := by
    have h1 : 2 * γ * ∑ i ∈ Finset.range n, ((i : ℝ) + 1) * E i ≤
        ∑ i ∈ Finset.range n, ((i : ℝ) + 1) * (‖z i - x‖ ^ 2 - ‖z (i + 1) - x‖ ^ 2)
        + γ ^ 2 * ∑ i ∈ Finset.range n, ((i : ℝ) + 1) * c i
        + 2 * γ * ⟪∑ i ∈ Finset.range n, ((i : ℝ) + 1) • (z i - z (i + 1)), gs⟫_ℝ := by
      rw [Finset.mul_sum, Finset.mul_sum, sum_inner, Finset.mul_sum, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro i _
      rw [real_inner_smul_left]
      have := mul_le_mul_of_nonneg_left (hstep i) (by positivity : (0:ℝ) ≤ (i : ℝ) + 1)
      nlinarith
    have h2 := WeightedAverage.telescope_weighted (fun i => ‖z i - x‖ ^ 2) n
    have h3 : ∑ i ∈ Finset.range n, ‖z i - x‖ ^ 2 ≤ (n : ℝ) * M1 ^ 2 := by
      calc ∑ i ∈ Finset.range n, ‖z i - x‖ ^ 2 ≤ ∑ _i ∈ Finset.range n, M1 ^ 2 :=
            Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hzx i) 2)
        _ = (n : ℝ) * M1 ^ 2 := by simp
    have h4 : ∑ i ∈ Finset.range n, ((i : ℝ) + 1) * c i ≤ (n : ℝ) * S := by
      calc ∑ i ∈ Finset.range n, ((i : ℝ) + 1) * c i ≤ ∑ i ∈ Finset.range n, (n : ℝ) * c i := by
            apply Finset.sum_le_sum; intro i hi
            apply mul_le_mul_of_nonneg_right _ (hc0 i)
            have := Finset.mem_range.1 hi
            have : (i : ℝ) + 1 ≤ n := by exact_mod_cast this
            linarith
        _ = (n : ℝ) * ∑ i ∈ Finset.range n, c i := by rw [Finset.mul_sum]
        _ ≤ (n : ℝ) * S := mul_le_mul_of_nonneg_left (hpart n) (by positivity)
    have h5 : ∑ i ∈ Finset.range n, ((i : ℝ) + 1) • (z i - z (i + 1)) =
        -((n : ℝ) • (z n - zstar) - ∑ i ∈ Finset.range n, (z i - zstar)) := by
      rw [← WeightedAverage.abel_sum z zstar n, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl; intro i _; rw [← smul_neg, neg_sub]
    have h6 : ‖(n : ℝ) • (z n - zstar) - ∑ i ∈ Finset.range n, (z i - zstar)‖ ≤
        2 * (n : ℝ) * ‖z0 - zstar‖ := by
      have hd : ∀ j, ‖z j - zstar‖ ≤ ‖z0 - zstar‖ := fun j => hfej (Nat.zero_le j)
      have q1 := norm_sub_le ((n : ℝ) • (z n - zstar)) (∑ i ∈ Finset.range n, (z i - zstar))
      have q2 : ‖(n : ℝ) • (z n - zstar)‖ ≤ (n : ℝ) * ‖z0 - zstar‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_left (hd n) (by positivity)
      have q3 : ‖∑ i ∈ Finset.range n, (z i - zstar)‖ ≤ (n : ℝ) * ‖z0 - zstar‖ := by
        calc ‖∑ i ∈ Finset.range n, (z i - zstar)‖ ≤ ∑ i ∈ Finset.range n, ‖z i - zstar‖ :=
              norm_sum_le _ _
          _ ≤ ∑ _i ∈ Finset.range n, ‖z0 - zstar‖ := Finset.sum_le_sum (fun i _ => hd i)
          _ = (n : ℝ) * ‖z0 - zstar‖ := by simp
      linarith
    have h7 : ⟪∑ i ∈ Finset.range n, ((i : ℝ) + 1) • (z i - z (i + 1)), gs⟫_ℝ ≤
        2 * (n : ℝ) * ‖z0 - zstar‖ * ‖gs‖ := by
      rw [h5, inner_neg_left]
      have := abs_real_inner_le_norm ((n : ℝ) • (z n - zstar) - ∑ i ∈ Finset.range n, (z i - zstar)) gs
      have := (abs_le.1 this).1
      have := mul_le_mul_of_nonneg_right h6 (norm_nonneg gs)
      linarith
    have hDn : 0 ≤ (n : ℝ) * ‖z n - x‖ ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left h4 (sq_nonneg γ)
    have := mul_le_mul_of_nonneg_left h7 (by positivity : (0:ℝ) ≤ 2 * γ)
    rw [hQ]
    nlinarith
  -- weights
  have hn0 : (0 : ℝ) < n := by rw [hn]; positivity
  set W := 2 / ((n : ℝ) * ((n : ℝ) + 1)) with hW
  have hWpos : 0 < W := by positivity
  have hwe : ∀ y : ℕ → H, weightedErgodic y k = ∑ i ∈ Finset.range n, (W * ((i : ℝ) + 1)) • y i := by
    intro y
    simp only [weightedErgodic, Finset.smul_sum, smul_smul]
    have e : ((k : ℝ) + 1) * ((k : ℝ) + 2) = (n : ℝ) * ((n : ℝ) + 1) := by rw [hn]; push_cast; ring
    rw [e]
  have hw0 : ∀ i ∈ Finset.range n, 0 ≤ W * ((i : ℝ) + 1) := fun i _ => by positivity
  have hw1 : ∑ i ∈ Finset.range n, W * ((i : ℝ) + 1) = 1 := by
    rw [← Finset.mul_sum, WeightedAverage.gauss_real, hW]; field_simp
  -- averages lie in the ball
  have hconvB := convex_closedBall x r
  have hxgbar : weightedErgodic xg k ∈ Metric.closedBall x r := by
    rw [hwe]; exact hconvB.sum_mem hw0 hw1 (fun i _ => (hball i).2)
  have hxfbar : weightedErgodic xf k ∈ Metric.closedBall x r := by
    rw [hwe]; exact hconvB.sum_mem hw0 hw1 (fun i _ => (hball i).1)
  -- Jensen
  have jf := ERealFn.jensen_finite_sum f hfconv (Finset.range n) (fun i => W * ((i : ℝ) + 1)) xf a hw0 hw1
    (fun i _ => efa i)
  have jg := ERealFn.jensen_finite_sum g hgconv (Finset.range n) (fun i => W * ((i : ℝ) + 1)) xg b hw0 hw1
    (fun i _ => egb i)
  rw [← hwe] at jf jg
  have jh := hh.1.map_sum_le (t := Finset.range n) (w := fun i => W * ((i : ℝ) + 1)) (p := xg)
    hw0 hw1 (fun i _ => Set.mem_univ _)
  rw [← hwe] at jh
  simp only [smul_eq_mul] at jh
  -- finiteness at the averages
  have fbar : f (weightedErgodic xg k) ≠ ⊤ := hfin _ hxgbar
  have fbar' : f (weightedErgodic xf k) ≠ ⊤ := hfin _ hxfbar
  have gbar : g (weightedErgodic xg k) ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) jg
  rw [hobj _ fbar gbar, hobj x fx gx, ← hFs, ← EReal.coe_add, EReal.coe_le_coe_iff]
  -- real inequalities
  have jf' : (f (weightedErgodic xf k)).toReal ≤ ∑ i ∈ Finset.range n, W * ((i : ℝ) + 1) * a i := by
    rw [← EReal.coe_le_coe_iff, EReal.coe_toReal fbar' (hfb _)]; exact jf
  have jg' : (g (weightedErgodic xg k)).toReal ≤ ∑ i ∈ Finset.range n, W * ((i : ℝ) + 1) * b i := by
    rw [← EReal.coe_le_coe_iff, EReal.coe_toReal gbar (hgb _)]; exact jg
  have hL := hLip.dist_le_mul _ hxgbar _ hxfbar
  rw [Real.dist_eq, dist_eq_norm] at hL
  have hL' := (abs_le.1 hL).2
  have hdist := hwed k
  rw [norm_sub_rev] at hdist
  have hLd : (L : ℝ) * ‖weightedErgodic xg k - weightedErgodic xf k‖ ≤
      (L : ℝ) * (5 * ‖z0 - zstar‖ / ((k : ℝ) + 1)) :=
    mul_le_mul_of_nonneg_left hdist L.coe_nonneg
  -- combine
  have hsumW : ∑ i ∈ Finset.range n, W * ((i : ℝ) + 1) * a i
      + ∑ i ∈ Finset.range n, W * ((i : ℝ) + 1) * b i
      + ∑ i ∈ Finset.range n, W * ((i : ℝ) + 1) * h (xg i) - Fs
      = W * ∑ i ∈ Finset.range n, ((i : ℝ) + 1) * E i := by
    have hF : Fs = ∑ i ∈ Finset.range n, W * ((i : ℝ) + 1) * Fs := by
      rw [← Finset.sum_mul, hw1, one_mul]
    rw [hF, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _
    simp only [hE]; ring
  have hWE : W * ∑ i ∈ Finset.range n, ((i : ℝ) + 1) * E i ≤ Q / γ / ((k : ℝ) + 1) := by
    have h1 : ∑ i ∈ Finset.range n, ((i : ℝ) + 1) * E i ≤ (n : ℝ) * Q / (2 * γ) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hWpos.le
    have e : W * ((n : ℝ) * Q / (2 * γ)) = Q / γ / ((n : ℝ) + 1) := by
      rw [hW]; field_simp
    rw [e] at h2
    have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
    have h3 : Q / γ / ((n : ℝ) + 1) ≤ Q / γ / ((k : ℝ) + 1) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      rw [hn]; push_cast; linarith
    linarith
  have hfin' : Fs + (Q / γ + 5 * ↑L * ‖z0 - zstar‖) / ((k : ℝ) + 1) =
      Fs + Q / γ / ((k : ℝ) + 1) + (L : ℝ) * (5 * ‖z0 - zstar‖ / ((k : ℝ) + 1)) := by
    field_simp; ring
  rw [hfin']
  linarith
