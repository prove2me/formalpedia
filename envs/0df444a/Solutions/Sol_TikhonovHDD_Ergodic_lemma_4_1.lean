-- Prove2me | solution 1 for TikhonovHDD.Ergodic.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T04:21:01.653195+00:00
-- url     : https://prove2.me/submissions/1e7c68bd-f09d-43c6-9679-65a09c96043f

import Mathlib
import Definitions.Def_TikhonovHDD_Ergodic_TikhonovCurve
import Definitions.Def_TikhonovHDD_Ergodic_Setting

open Set Filter Topology MeasureTheory

namespace TikhL41Aux

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Gradient inequality of a differentiable convex function. -/
lemma grad_ineq [CompleteSpace H] (g : H → ℝ) (hconv : ConvexOn ℝ univ g) (hdiff : Differentiable ℝ g)
    (a b : H) : g a + inner ℝ (gradient g a) (b - a) ≤ g b := by
  set φ : ℝ → ℝ := fun τ => g (a + τ • (b - a)) with hφ
  have hφc : ConvexOn ℝ univ φ := by
    refine ⟨convex_univ, fun r _ s _ p q hp hq hpq => ?_⟩
    have h := hconv.2 (mem_univ (a + r • (b - a))) (mem_univ (a + s • (b - a))) hp hq hpq
    have heq : p • (a + r • (b - a)) + q • (a + s • (b - a)) = a + (p • r + q • s) • (b - a) := by
      rw [smul_add, smul_add, smul_smul, smul_smul, add_add_add_comm, ← add_smul, hpq, one_smul,
        ← add_smul]
      simp [smul_eq_mul]
    simp only [hφ]
    rw [← heq]
    exact h
  have hline : HasDerivAt (fun τ : ℝ => a + τ • (b - a)) (b - a) 0 := by
    have := ((hasDerivAt_id (0:ℝ)).smul_const (b - a)).const_add a
    simpa using this
  have hd : HasDerivAt φ (inner ℝ (gradient g a) (b - a)) 0 := by
    have h1 := (hdiff (a + (0:ℝ) • (b - a))).hasGradientAt.hasFDerivAt.comp_hasDerivAt (0:ℝ) hline
    simp only [zero_smul, add_zero] at h1
    simpa [Function.comp_def, InnerProductSpace.toDual_apply_apply] using h1
  have := hφc.le_slope_of_hasDerivAt (mem_univ 0) (mem_univ 1) zero_lt_one hd
  simp [slope, hφ] at this
  have e1 : inner ℝ (gradient g a) (b - a) = fderiv ℝ g a b - fderiv ℝ g a a := by
    rw [inner_gradient_left, map_sub]
  linarith


/-- The Hessian of a convex twice differentiable function is positive semidefinite. -/
lemma hess_psd [CompleteSpace H] (g : H → ℝ) (hconv : ConvexOn ℝ univ g)
    (hdiff : Differentiable ℝ g) (hdiff2 : Differentiable ℝ (gradient g)) (y v : H) :
    0 ≤ inner ℝ (fderiv ℝ (gradient g) y v) v := by
  set φ : ℝ → ℝ := fun τ => inner ℝ (gradient g (y + τ • v)) v with hφ
  have hmono : Monotone φ := by
    intro τ1 τ2 h12
    rcases eq_or_lt_of_le h12 with h | h
    · rw [h]
    · have e1 := grad_ineq g hconv hdiff (y + τ2 • v) (y + τ1 • v)
      have e2 := grad_ineq g hconv hdiff (y + τ1 • v) (y + τ2 • v)
      have d1 : (y + τ1 • v) - (y + τ2 • v) = (τ1 - τ2) • v := by rw [sub_smul]; abel
      have d2 : (y + τ2 • v) - (y + τ1 • v) = (τ2 - τ1) • v := by rw [sub_smul]; abel
      rw [d1, inner_smul_right] at e1
      rw [d2, inner_smul_right] at e2
      simp only [hφ]
      by_contra hc
      push Not at hc
      nlinarith
  have hline : HasDerivAt (fun τ : ℝ => y + τ • v) v 0 := by
    have := ((hasDerivAt_id (0:ℝ)).smul_const v).const_add y
    simpa using this
  have hG : HasDerivAt (fun τ : ℝ => gradient g (y + τ • v)) (fderiv ℝ (gradient g) y v) 0 := by
    have h1 := (hdiff2 (y + (0:ℝ) • v)).hasFDerivAt.comp_hasDerivAt (0:ℝ) hline
    simp only [zero_smul, add_zero] at h1
    exact h1
  have hd : HasDerivAt φ (inner ℝ (fderiv ℝ (gradient g) y v) v) 0 := by
    have := hG.inner ℝ (hasDerivAt_const (0:ℝ) v)
    simp only [inner_zero_right, zero_add] at this
    exact this
  exact hd.nonneg_of_monotone hmono

end TikhL41Aux

open TikhonovHDD.Ergodic TikhL41Aux in
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (g : H → ℝ) (α β t₀ : ℝ) (ε ε' : ℝ → ℝ) (u₀ v₀ : H) (x xd xdd : ℝ → H)
    (ht₀ : 0 < t₀) (hα : 0 < α) (hβ : 0 ≤ β)
    (hg : GeneralAssumptionG g) (hε : GeneralAssumptionEps t₀ ε ε')
    (hx : IsSolution g α β ε t₀ u₀ v₀ x xd xdd) :
    BddAbove ((fun t => ‖xd t‖) '' Ici t₀) ∧
      IntegrableOn (fun t => ‖xd t‖ ^ 2 / t) (Ici t₀) ∧
      ∀ xstar ∈ TikhonovHDD.Strong.argminSet g, BddAbove ((fun t => |hDot x xd xstar t| / t) '' Ici t₀) := by
  obtain ⟨hconv, hdiff, hdiff2, -, ⟨xh, hxh⟩⟩ := hg
  obtain ⟨hεd, hε'c, hεnn, hεanti, -⟩ := hε
  obtain ⟨hxode, hxddc, -, -⟩ := hx
  have gcont : Continuous g := hdiff.continuous
  have Gcont : Continuous (gradient g) := hdiff2.continuous
  have xcont : ContinuousOn x (Ici t₀) := fun t ht => (hxode t ht).1.continuousWithinAt
  have xdcont : ContinuousOn xd (Ici t₀) := fun t ht => (hxode t ht).2.1.continuousWithinAt
  have εcont : ContinuousOn ε (Ici t₀) := fun t ht => (hεd t ht).continuousWithinAt
  have spos : ∀ s, t₀ ≤ s → 0 < s := fun s hs => lt_of_lt_of_le ht₀ hs
  have hsub : ∀ a b : ℝ, t₀ ≤ a → t₀ ≤ b → uIcc a b ⊆ Ici t₀ :=
    fun a b ha hb s hs => le_trans (le_min ha hb) hs.1
  -- ε' ≤ 0
  have hε'nonpos : ∀ s, t₀ ≤ s → ε' s ≤ 0 := by
    intro s hs
    have hacc : AccPt s (𝓟 (Ici t₀)) := by
      rw [accPt_principal_iff_nhdsWithin]
      refine NeBot.mono (inferInstance : (𝓝[>] s).NeBot) (nhdsWithin_mono s ?_)
      intro r hr
      exact ⟨le_trans hs (le_of_lt hr), ne_of_gt hr⟩
    exact (hεd s hs).nonpos_of_antitoneOn hacc hεanti
  -- energy
  obtain ⟨W, hW⟩ : ∃ W : ℝ → ℝ, W = fun r => g (x r) + 1 / 2 * ‖xd r‖ ^ 2 + ε r / 2 * ‖x r‖ ^ 2 :=
    ⟨_, rfl⟩
  obtain ⟨W', hW'⟩ : ∃ W' : ℝ → ℝ, W' = fun r => inner ℝ (gradient g (x r)) (xd r)
      + 1 / 2 * (2 * inner ℝ (xd r) (xdd r))
      + (ε' r / 2 * ‖x r‖ ^ 2 + ε r / 2 * (2 * inner ℝ (x r) (xd r))) := ⟨_, rfl⟩
  have hWd : ∀ s ∈ Ici t₀, HasDerivWithinAt W (W' s) (Ici t₀) s := by
    intro s hs
    obtain ⟨hx1, hx2, -⟩ := hxode s hs
    have hgd : HasDerivWithinAt (fun r => g (x r)) (inner ℝ (gradient g (x s)) (xd s)) (Ici t₀) s := by
      have := (hdiff (x s)).hasFDerivAt.comp_hasDerivWithinAt s hx1
      rw [inner_gradient_left]
      exact this
    have h2 := (hx2.norm_sq).const_mul (1/2 : ℝ)
    have h3 := ((hεd s hs).div_const 2).mul (hx1.norm_sq)
    rw [hW, hW']
    exact (hgd.add h2).add h3
  have W'cont : ContinuousOn W' (Ici t₀) := by
    rw [hW']
    refine ((Gcont.comp_continuousOn xcont).inner xdcont |>.add
      (continuousOn_const.mul (continuousOn_const.mul (xdcont.inner hxddc)))).add ?_
    exact ((hε'c.div_const 2).mul ((continuous_norm.comp_continuousOn xcont).pow 2)).add
      ((εcont.div_const 2).mul (continuousOn_const.mul (xcont.inner xdcont)))
  have Wcont : ContinuousOn W (Ici t₀) := fun s hs => (hWd s hs).continuousWithinAt
  -- pointwise dissipation
  have hdis : ∀ s, t₀ ≤ s → W' s ≤ -(α * (‖xd s‖ ^ 2 / s)) := by
    intro s hs
    obtain ⟨-, -, hode⟩ := hxode s hs
    have sp := spos s hs
    set Hv := fderiv ℝ (gradient g) (x s) (xd s)
    have hpsd := hess_psd g hconv hdiff hdiff2 (x s) (xd s)
    have hxdd : xdd s = -((α / s) • xd s + β • Hv + gradient g (x s) + ε s • x s) := by
      rw [eq_neg_iff_add_eq_zero, ← hode]; abel
    have hin : inner ℝ (xd s) (xdd s) = -((α / s) * ‖xd s‖ ^ 2 + β * inner ℝ Hv (xd s)
        + inner ℝ (gradient g (x s)) (xd s) + ε s * inner ℝ (x s) (xd s)) := by
      rw [hxdd, inner_neg_right]
      simp only [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq]
      rw [real_inner_comm Hv, real_inner_comm (gradient g (x s)), real_inner_comm (x s)]
    rw [hW']
    show inner ℝ (gradient g (x s)) (xd s) + 1 / 2 * (2 * inner ℝ (xd s) (xdd s))
      + (ε' s / 2 * ‖x s‖ ^ 2 + ε s / 2 * (2 * inner ℝ (x s) (xd s))) ≤ _
    rw [hin]
    have e1 := hε'nonpos s hs
    have e2 : 0 ≤ β * inner ℝ Hv (xd s) := mul_nonneg hβ hpsd
    have e3 : ε' s / 2 * ‖x s‖ ^ 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)
    have e4 : α / s * ‖xd s‖ ^ 2 = α * (‖xd s‖ ^ 2 / s) := by ring
    linarith
  have kcont : ContinuousOn (fun s => ‖xd s‖ ^ 2 / s) (Ici t₀) :=
    ((continuous_norm.comp_continuousOn xdcont).pow 2).div continuousOn_id
      (fun s hs => ne_of_gt (spos s hs))
  -- integrated energy estimate
  have hWlow : ∀ t, t₀ ≤ t → g xh + 1 / 2 * ‖xd t‖ ^ 2 ≤ W t := by
    intro t ht
    rw [hW]
    have := hxh (x t)
    have : 0 ≤ ε t / 2 * ‖x t‖ ^ 2 := mul_nonneg (div_nonneg (hεnn t ht) (by norm_num)) (sq_nonneg _)
    show g xh + 1 / 2 * ‖xd t‖ ^ 2 ≤ g (x t) + 1 / 2 * ‖xd t‖ ^ 2 + ε t / 2 * ‖x t‖ ^ 2
    linarith
  have hEI : ∀ t, t₀ ≤ t → W t + α * ∫ s in t₀..t, ‖xd s‖ ^ 2 / s ≤ W t₀ := by
    intro t ht
    have hsb := hsub t₀ t le_rfl ht
    have kII : IntervalIntegrable (fun s => ‖xd s‖ ^ 2 / s) volume t₀ t :=
      (kcont.mono hsb).intervalIntegrable
    have W'II : IntervalIntegrable W' volume t₀ t := (W'cont.mono hsb).intervalIntegrable
    have hftc : ∫ s in t₀..t, W' s = W t - W t₀ := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht (Wcont.mono Icc_subset_Ici_self)
      · intro s hs
        exact (hWd s (le_of_lt hs.1)).hasDerivAt (Ici_mem_nhds hs.1)
      · exact W'II
    have nII : IntervalIntegrable (fun s => -(α * (‖xd s‖ ^ 2 / s))) volume t₀ t :=
      (kII.const_mul α).neg
    have hmono := intervalIntegral.integral_mono_on ht W'II nII (fun s hs => hdis s hs.1)
    rw [hftc, intervalIntegral.integral_neg, intervalIntegral.integral_const_mul] at hmono
    linarith
  have kint_nn : ∀ t, t₀ ≤ t → 0 ≤ ∫ s in t₀..t, ‖xd s‖ ^ 2 / s := fun t ht =>
    intervalIntegral.integral_nonneg ht fun s hs => div_nonneg (sq_nonneg _) (spos s hs.1).le
  set M := W t₀ - g xh with hM
  have hM0 : 0 ≤ M := by have := hWlow t₀ le_rfl; nlinarith [sq_nonneg ‖xd t₀‖]
  -- velocity bound
  set K := 2 * M + 1 with hK
  have hKb : ∀ t, t₀ ≤ t → ‖xd t‖ ≤ K := by
    intro t ht
    have h1 := hWlow t ht
    have h2 := hEI t ht
    have h3 := kint_nn t ht
    have h4 : ‖xd t‖ ^ 2 ≤ 2 * M := by nlinarith
    nlinarith [sq_nonneg (‖xd t‖ - 1)]
  refine ⟨⟨K, ?_⟩, ?_, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    exact hKb t ht
  · rw [integrableOn_Ici_iff_integrableOn_Ioi]
    refine integrableOn_Ioi_of_intervalIntegral_norm_bounded (M / α) t₀ (b := id) ?_ tendsto_id ?_
    · intro i
      have : IntegrableOn (fun s => ‖xd s‖ ^ 2 / s) (Icc t₀ (max t₀ i)) volume :=
        (kcont.mono Icc_subset_Ici_self).integrableOn_Icc
      exact this.mono_set (Ioc_subset_Icc_self.trans (Icc_subset_Icc le_rfl (le_max_right _ _)))
    · filter_upwards [eventually_ge_atTop t₀] with i hi
      have heq : ∫ s in t₀..id i, ‖‖xd s‖ ^ 2 / s‖ = ∫ s in t₀..i, ‖xd s‖ ^ 2 / s := by
        apply intervalIntegral.integral_congr
        intro s hs
        have hs' : s ∈ uIcc t₀ i := hs
        rw [uIcc_of_le hi] at hs'
        exact Real.norm_of_nonneg (div_nonneg (sq_nonneg _) (spos s hs'.1).le)
      rw [heq, le_div_iff₀ hα]
      have h1 := hWlow i hi
      have h2 := hEI i hi
      nlinarith [sq_nonneg ‖xd i‖]
  · intro xstar _
    refine ⟨K * (‖x t₀ - xstar‖ / t₀ + K), ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    have ht' : t₀ ≤ t := ht
    have tp := spos t ht'
    have hmv := norm_image_sub_le_of_norm_deriv_le_segment' (f := x) (f' := xd) (C := K)
      (fun s hs => ((hxode s hs.1).1).mono Icc_subset_Ici_self)
      (fun s hs => hKb s hs.1) t ⟨ht', le_rfl⟩
    have hdist : ‖x t - xstar‖ ≤ K * (t - t₀) + ‖x t₀ - xstar‖ := by
      have := norm_sub_le_norm_sub_add_norm_sub (x t) (x t₀) xstar
      linarith
    have hK0 : 0 ≤ K := by linarith
    have hin : |hDot x xd xstar t| ≤ K * (K * (t - t₀) + ‖x t₀ - xstar‖) := by
      calc |hDot x xd xstar t| ≤ ‖xd t‖ * ‖x t - xstar‖ := abs_real_inner_le_norm _ _
        _ ≤ K * (K * (t - t₀) + ‖x t₀ - xstar‖) :=
          mul_le_mul (hKb t ht') hdist (norm_nonneg _) hK0
    have hA : ‖x t₀ - xstar‖ ≤ ‖x t₀ - xstar‖ / t₀ * t := by
      rw [div_mul_eq_mul_div, le_div_iff₀ ht₀]
      nlinarith [norm_nonneg (x t₀ - xstar)]
    show |hDot x xd xstar t| / t ≤ K * (‖x t₀ - xstar‖ / t₀ + K)
    rw [div_le_iff₀ tp]
    have h1 := mul_le_mul_of_nonneg_left hA hK0
    have h2 := mul_nonneg (mul_nonneg hK0 hK0) ht₀.le
    have h3 : K * (‖x t₀ - xstar‖ / t₀ + K) * t
        = K * (‖x t₀ - xstar‖ / t₀ * t) + K * K * t := by ring
    have h4 : K * (K * (t - t₀) + ‖x t₀ - xstar‖)
        = K * ‖x t₀ - xstar‖ + K * K * t - K * K * t₀ := by ring
    rw [h3]
    linarith
