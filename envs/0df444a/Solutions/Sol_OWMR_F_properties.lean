-- Prove2me | solution 1 for OWMR.F_properties
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-16T02:43:04.385207+00:00
-- url     : https://prove2.me/submissions/f24e31ea-1130-412c-871f-f1eb009abb05

import Definitions.Def_owmr_single_location

/-!
Regularity of the retailer cost `F_i` of (8), as used in Lemma 3 and in the footnote to (8):
`F_i ≥ 0`, `F_i` is convex, `F_i` is Lipschitz with constant `H_i + p`, and `F_i` has slopes at
least `-p`.
-/

open MeasureTheory
open scoped ENNReal NNReal
open OWMR

/-- A retailer's one-period demand has a finite first moment. -/
private lemma integrable_marginal {n : ℕ} (N : Network n) (hN : N.Standing) (i : Fin n) :
    Integrable (fun x : ℝ≥0 => (x : ℝ)) (N.marginal i) := by
  unfold Network.marginal
  rw [integrable_map_measure measurable_coe_nnreal_real.aestronglyMeasurable
    (measurable_pi_apply i).aemeasurable]
  have h := integrable_toReal_of_lintegral_ne_top
    (f := fun x : DemandVec n => ((x i : ℝ≥0) : ℝ≥0∞))
    ((measurable_pi_apply i).coe_nnreal_ennreal.aemeasurable) (hN.mean_lt_top i).ne
  simpa [Function.comp_def] using h

/-- The sum of `L` i.i.d. demands of a retailer is integrable. -/
private lemma integrable_sum {n : ℕ} (N : Network n) (hN : N.Standing) (i : Fin n) (L : ℕ) :
    Integrable (fun z : Fin L → ℝ≥0 => ∑ j, (z j : ℝ))
      (Measure.pi fun _ : Fin L => N.marginal i) := by
  refine integrable_finsetSum _ fun j _ => ?_
  have hmp := measurePreserving_eval (μ := fun _ : Fin L => N.marginal i) j
  exact (hmp.integrable_comp measurable_coe_nnreal_real.aestronglyMeasurable).2
    (integrable_marginal N hN i)

private lemma loss_lip (H p s y y' : ℝ) (hH : 0 ≤ H) (hp : 0 ≤ p) :
    |H * max (y - s) 0 + p * max (s - y) 0 - (H * max (y' - s) 0 + p * max (s - y') 0)|
      ≤ (H + p) * |y - y'| := by
  have k1 := abs_max_sub_max_le_abs (y - s) (y' - s) 0
  have k2 := abs_max_sub_max_le_abs (s - y) (s - y') 0
  rw [show y - s - (y' - s) = y - y' by ring] at k1
  rw [show s - y - (s - y') = -(y - y') by ring, abs_neg] at k2
  calc |H * max (y - s) 0 + p * max (s - y) 0 - (H * max (y' - s) 0 + p * max (s - y') 0)|
      = |H * (max (y - s) 0 - max (y' - s) 0) + p * (max (s - y) 0 - max (s - y') 0)| := by
        ring_nf
    _ ≤ |H * (max (y - s) 0 - max (y' - s) 0)| + |p * (max (s - y) 0 - max (s - y') 0)| :=
        abs_add_le _ _
    _ = H * |max (y - s) 0 - max (y' - s) 0| + p * |max (s - y) 0 - max (s - y') 0| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hH, abs_of_nonneg hp]
    _ ≤ H * |y - y'| + p * |y - y'| :=
        add_le_add (mul_le_mul_of_nonneg_left k1 hH) (mul_le_mul_of_nonneg_left k2 hp)
    _ = (H + p) * |y - y'| := by ring

private lemma loss_convex (H p s x y a b : ℝ) (hH : 0 ≤ H) (hp : 0 ≤ p) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hab : a + b = 1) :
    H * max (a * x + b * y - s) 0 + p * max (s - (a * x + b * y)) 0
      ≤ a * (H * max (x - s) 0 + p * max (s - x) 0) + b * (H * max (y - s) 0 + p * max (s - y) 0) := by
  have hs : a * s + b * s = s := by rw [← add_mul, hab, one_mul]
  have k1 : max (a * x + b * y - s) 0 ≤ a * max (x - s) 0 + b * max (y - s) 0 := by
    refine max_le ?_ (add_nonneg (mul_nonneg ha (le_max_right _ _)) (mul_nonneg hb (le_max_right _ _)))
    have := mul_le_mul_of_nonneg_left (le_max_left (x - s) 0) ha
    have := mul_le_mul_of_nonneg_left (le_max_left (y - s) 0) hb
    linarith
  have k2 : max (s - (a * x + b * y)) 0 ≤ a * max (s - x) 0 + b * max (s - y) 0 := by
    refine max_le ?_ (add_nonneg (mul_nonneg ha (le_max_right _ _)) (mul_nonneg hb (le_max_right _ _)))
    have := mul_le_mul_of_nonneg_left (le_max_left (s - x) 0) ha
    have := mul_le_mul_of_nonneg_left (le_max_left (s - y) 0) hb
    linarith
  have := mul_le_mul_of_nonneg_left k1 hH
  have := mul_le_mul_of_nonneg_left k2 hp
  linarith

private lemma loss_slope (H p s y y' : ℝ) (hH : 0 ≤ H) (hp : 0 ≤ p) (hyy' : y ≤ y') :
    H * max (y - s) 0 + p * max (s - y) 0 - p * (y' - y)
      ≤ H * max (y' - s) 0 + p * max (s - y') 0 := by
  have k1 : max (y - s) 0 ≤ max (y' - s) 0 := max_le_max (by linarith) le_rfl
  have k2 : max (s - y) 0 ≤ max (s - y') 0 + (y' - y) := by
    refine max_le ?_ (by linarith [le_max_right (s - y') 0])
    linarith [le_max_left (s - y') 0]
  have := mul_le_mul_of_nonneg_left k1 hH
  have := mul_le_mul_of_nonneg_left k2 hp
  linarith

theorem solution {n : ℕ} (N : Network n) (hN : N.Standing) (i : Fin n) :
    (∀ y, 0 ≤ N.F i y) ∧ ConvexOn ℝ Set.univ (N.F i) ∧
      (∀ y y', |N.F i y - N.F i y'| ≤ (N.H i + N.p) * |y - y'|) ∧
      (∀ y y', y ≤ y' → N.F i y - N.p * (y' - y) ≤ N.F i y') := by
  have hH : 0 < N.H i := hN.H_pos i
  have hp : 0 < N.p := hN.p_pos
  have hu := integrable_sum N hN i (N.L i + 1)
  have hφ : ∀ y, Integrable (fun z : Fin (N.L i + 1) → ℝ≥0 =>
      N.H i * max (y - ∑ j, (z j : ℝ)) 0 + N.p * max (∑ j, (z j : ℝ) - y) 0)
      (Measure.pi fun _ : Fin (N.L i + 1) => N.marginal i) := fun y =>
    (((integrable_const y).sub hu).pos_part.const_mul _).add
      ((hu.sub (integrable_const y)).pos_part.const_mul _)
  refine ⟨fun y => ?_, ?_, fun y y' => ?_, fun y y' hyy' => ?_⟩
  · exact integral_nonneg fun z =>
      add_nonneg (mul_nonneg hH.le (le_max_right _ _)) (mul_nonneg hp.le (le_max_right _ _))
  · refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    simp only [smul_eq_mul]
    unfold Network.F
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add ((hφ x).const_mul a) ((hφ y).const_mul b)]
    exact integral_mono (hφ _) (((hφ x).const_mul a).add ((hφ y).const_mul b)) fun z =>
      loss_convex _ _ _ _ _ _ _ hH.le hp.le ha hb hab
  · unfold Network.F
    rw [← integral_sub (hφ y) (hφ y')]
    calc |∫ z, (N.H i * max (y - ∑ j, (z j : ℝ)) 0 + N.p * max (∑ j, (z j : ℝ) - y) 0
            - (N.H i * max (y' - ∑ j, (z j : ℝ)) 0 + N.p * max (∑ j, (z j : ℝ) - y') 0))
            ∂(Measure.pi fun _ : Fin (N.L i + 1) => N.marginal i)|
        ≤ ∫ z, |N.H i * max (y - ∑ j, (z j : ℝ)) 0 + N.p * max (∑ j, (z j : ℝ) - y) 0
            - (N.H i * max (y' - ∑ j, (z j : ℝ)) 0 + N.p * max (∑ j, (z j : ℝ) - y') 0)|
            ∂(Measure.pi fun _ : Fin (N.L i + 1) => N.marginal i) :=
          abs_integral_le_integral_abs
      _ ≤ ∫ _z, (N.H i + N.p) * |y - y'|
            ∂(Measure.pi fun _ : Fin (N.L i + 1) => N.marginal i) :=
          integral_mono ((hφ y).sub (hφ y')).abs (integrable_const _) fun z =>
            loss_lip _ _ _ _ _ hH.le hp.le
      _ = (N.H i + N.p) * |y - y'| := by simp [integral_const, probReal_univ]
  · unfold Network.F
    have e : ∫ z, (N.H i * max (y - ∑ j, (z j : ℝ)) 0 + N.p * max (∑ j, (z j : ℝ) - y) 0
        - N.p * (y' - y)) ∂(Measure.pi fun _ : Fin (N.L i + 1) => N.marginal i)
        = (∫ z, (N.H i * max (y - ∑ j, (z j : ℝ)) 0 + N.p * max (∑ j, (z j : ℝ) - y) 0)
          ∂(Measure.pi fun _ : Fin (N.L i + 1) => N.marginal i)) - N.p * (y' - y) := by
      rw [integral_sub (hφ y) (integrable_const _), integral_const]
      simp [probReal_univ]
    rw [← e]
    exact integral_mono ((hφ y).sub (integrable_const _)) (hφ y') fun z =>
      loss_slope _ _ _ _ _ hH.le hp.le hyy'
