-- Prove2me | solution 1 for TikhonovHDD.Ergodic.tikhonov_curve_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T04:05:58.134105+00:00
-- url     : https://prove2.me/submissions/c9d43048-f906-40ed-b128-d7321fa9ffd2

import Mathlib
import Definitions.Def_TikhonovHDD_Ergodic_TikhonovCurve
import Definitions.Def_TikhonovHDD_Ergodic_Setting

open Set Filter Topology MeasureTheory

namespace TikhCurveAux

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma mid_norm_sq (a b : H) :
    ‖(1/2 : ℝ) • a + (1/2 : ℝ) • b‖ ^ 2 = (‖a‖ ^ 2 + ‖b‖ ^ 2) / 2 - ‖a - b‖ ^ 2 / 4 := by
  have h1 : (1/2 : ℝ) • a + (1/2 : ℝ) • b = (1/2 : ℝ) • (a + b) := by
    rw [smul_add]
  rw [h1, norm_smul, mul_pow, norm_add_sq_real, norm_sub_sq_real]
  norm_num
  ring

/-- Midpoint strong-convexity inequality for `g + (e/2)‖·‖²`. -/
lemma mid_ineq (g : H → ℝ) (hconv : ConvexOn ℝ univ g) (e : ℝ) (_he : 0 ≤ e) (a b : H) :
    g ((1/2 : ℝ) • a + (1/2 : ℝ) • b) + e / 2 * ‖(1/2 : ℝ) • a + (1/2 : ℝ) • b‖ ^ 2 ≤
      ((g a + e / 2 * ‖a‖ ^ 2) + (g b + e / 2 * ‖b‖ ^ 2)) / 2 - e / 8 * ‖a - b‖ ^ 2 := by
  have hc := hconv.2 (mem_univ a) (mem_univ b) (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  simp only [smul_eq_mul] at hc
  rw [mid_norm_sq]
  nlinarith

/-- Quadratic growth around a Tikhonov point. -/
lemma quad_growth (g : H → ℝ) (hconv : ConvexOn ℝ univ g) (e : ℝ) (he : 0 ≤ e) (y : H)
    (hy : TikhonovHDD.Ergodic.IsTikhonovPoint g e y) (z : H) :
    g y + e / 2 * ‖y‖ ^ 2 + e / 4 * ‖z - y‖ ^ 2 ≤ g z + e / 2 * ‖z‖ ^ 2 := by
  have h1 := mid_ineq g hconv e he z y
  have h2 := hy ((1/2 : ℝ) • z + (1/2 : ℝ) • y)
  linarith

end TikhCurveAux

open TikhCurveAux in
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (g : H → ℝ) (hg : TikhonovHDD.Ergodic.GeneralAssumptionG g) (xstar : H)
    (hxstar : TikhonovHDD.Strong.IsMinNormMinimizer g xstar)
    (xε : ℝ → H) (hxε : ∀ e > 0, TikhonovHDD.Ergodic.IsTikhonovPoint g e (xε e)) :
    Tendsto xε (𝓝[>] 0) (𝓝 xstar) := by
  obtain ⟨hconv, hdiff, -, -, -⟩ := hg
  obtain ⟨hxs_min, hxs_norm⟩ := hxstar
  have gcont : Continuous g := hdiff.continuous
  -- norm bound
  have hnorm : ∀ e > 0, ‖xε e‖ ^ 2 ≤ ‖xstar‖ ^ 2 := by
    intro e he
    have h1 := hxε e he xstar
    have h2 := hxs_min (xε e)
    have : e / 2 * ‖xε e‖ ^ 2 ≤ e / 2 * ‖xstar‖ ^ 2 := by linarith
    exact le_of_mul_le_mul_left this (by linarith)
  -- key Cauchy estimate
  have hkey : ∀ a b : ℝ, 0 < b → b ≤ a →
      ‖xε a - xε b‖ ^ 2 ≤ 2 * (‖xε b‖ ^ 2 - ‖xε a‖ ^ 2) := by
    intro a b hb hba
    have ha : 0 < a := lt_of_lt_of_le hb hba
    have h1 := quad_growth g hconv b hb.le (xε b) (hxε b hb) (xε a)
    have h2 := quad_growth g hconv a ha.le (xε a) (hxε a ha) (xε b)
    rw [norm_sub_rev (xε b) (xε a)] at h2
    have hD := sq_nonneg ‖xε a - xε b‖
    rcases eq_or_lt_of_le hba with hab | hab
    · subst hab; simp
    · have hsum : (a + b) / 2 * ‖xε a - xε b‖ ^ 2 ≤ (a - b) * (‖xε b‖ ^ 2 - ‖xε a‖ ^ 2) := by
        linarith
      have hN : 0 ≤ ‖xε b‖ ^ 2 - ‖xε a‖ ^ 2 := by
        by_contra hc
        push_neg at hc
        have : (a - b) * (‖xε b‖ ^ 2 - ‖xε a‖ ^ 2) < 0 := mul_neg_of_pos_of_neg (by linarith) hc
        nlinarith
      have h3 : (a - b) * (‖xε b‖ ^ 2 - ‖xε a‖ ^ 2) ≤ (a + b) * (‖xε b‖ ^ 2 - ‖xε a‖ ^ 2) :=
        mul_le_mul_of_nonneg_right (by linarith) hN
      have h4 : (a + b) * ‖xε a - xε b‖ ^ 2 ≤ (a + b) * (2 * (‖xε b‖ ^ 2 - ‖xε a‖ ^ 2)) := by
        nlinarith
      exact le_of_mul_le_mul_left h4 (by linarith)
  have hanti : ∀ a b : ℝ, 0 < b → b ≤ a → ‖xε a‖ ^ 2 ≤ ‖xε b‖ ^ 2 := by
    intro a b hb hba
    have := hkey a b hb hba
    nlinarith [sq_nonneg ‖xε a - xε b‖]
  -- supremum of the norms
  set S : Set ℝ := (fun e => ‖xε e‖ ^ 2) '' Ioi 0 with hS
  have hSne : S.Nonempty := ⟨_, mem_image_of_mem _ (show (1:ℝ) ∈ Ioi 0 by norm_num)⟩
  have hSbdd : BddAbove S := by
    refine ⟨‖xstar‖ ^ 2, ?_⟩
    rintro _ ⟨e, he, rfl⟩
    exact hnorm e he
  set L := sSup S
  have hle_L : ∀ e > 0, ‖xε e‖ ^ 2 ≤ L := fun e he => le_csSup hSbdd (mem_image_of_mem _ he)
  -- Cauchy
  have hcauchy : Cauchy (map xε (𝓝[>] (0:ℝ))) := by
    rw [Metric.cauchy_iff]
    refine ⟨inferInstance, ?_⟩
    intro η hη
    obtain ⟨_, ⟨e0, he0, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup hSne
      (show L - η ^ 2 / 4 < L by nlinarith)
    refine ⟨xε '' Ioc 0 e0, image_mem_map (Ioc_mem_nhdsGT he0), ?_⟩
    have aux : ∀ a b : ℝ, a ∈ Ioc (0:ℝ) e0 → b ∈ Ioc (0:ℝ) e0 → b ≤ a →
        dist (xε a) (xε b) < η := by
      intro a b ha hb hba
      have h1 := hkey a b hb.1 hba
      have h2 := hanti e0 a ha.1 ha.2
      have h3 := hle_L b hb.1
      have hsq : dist (xε a) (xε b) ^ 2 < η ^ 2 := by
        rw [dist_eq_norm]; nlinarith
      exact lt_of_pow_lt_pow_left₀ 2 hη.le hsq
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rcases le_total b a with hba | hab
    · exact aux a b ha hb hba
    · rw [dist_comm]; exact aux b a hb ha hab
  obtain ⟨y, hy⟩ := CompleteSpace.complete hcauchy
  have hyt : Tendsto xε (𝓝[>] (0:ℝ)) (𝓝 y) := hy
  have hev : ∀ᶠ e in 𝓝[>] (0:ℝ), 0 < e := self_mem_nhdsWithin
  have hid : Tendsto (fun e : ℝ => e) (𝓝[>] (0:ℝ)) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  -- y ∈ argmin g
  have hymin : ∀ z, g y ≤ g z := by
    intro z
    have hl : Tendsto (fun e => g (xε e) + e / 2 * ‖xε e‖ ^ 2) (𝓝[>] (0:ℝ))
        (𝓝 (g y + 0 / 2 * ‖y‖ ^ 2)) :=
      ((gcont.tendsto y).comp hyt).add ((hid.div_const 2).mul
        ((continuous_norm.tendsto y).comp hyt |>.pow 2))
    have hr : Tendsto (fun e : ℝ => g z + e / 2 * ‖z‖ ^ 2) (𝓝[>] (0:ℝ))
        (𝓝 (g z + 0 / 2 * ‖z‖ ^ 2)) :=
      tendsto_const_nhds.add ((hid.div_const 2).mul tendsto_const_nhds)
    have := le_of_tendsto_of_tendsto hl hr (hev.mono fun e he => hxε e he z)
    simpa using this
  have hynorm : ‖y‖ ^ 2 ≤ ‖xstar‖ ^ 2 := by
    have hl : Tendsto (fun e => ‖xε e‖ ^ 2) (𝓝[>] (0:ℝ)) (𝓝 (‖y‖ ^ 2)) :=
      ((continuous_norm.tendsto y).comp hyt).pow 2
    exact le_of_tendsto hl (hev.mono fun e he => hnorm e he)
  -- uniqueness of the minimum norm element
  have hmid_min : ∀ z, g ((1/2 : ℝ) • y + (1/2 : ℝ) • xstar) ≤ g z := by
    intro z
    have hc := hconv.2 (mem_univ y) (mem_univ xstar) (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
    simp only [smul_eq_mul] at hc
    have := hymin z
    have := hxs_min z
    linarith
  have h1 := hxs_norm _ hmid_min
  have h1' : ‖xstar‖ ^ 2 ≤ ‖(1/2 : ℝ) • y + (1/2 : ℝ) • xstar‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  rw [mid_norm_sq] at h1'
  have hzero : ‖y - xstar‖ ^ 2 ≤ 0 := by linarith
  have : y = xstar := by
    have : ‖y - xstar‖ = 0 := by nlinarith [norm_nonneg (y - xstar)]
    exact sub_eq_zero.mp (norm_eq_zero.mp this)
  rw [← this]
  exact hyt
