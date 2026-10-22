-- Prove2me | solution 1 for SGDKaczmarz.SGD.theorem_2_1
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-22T00:43:11.369997+00:00
-- url     : https://prove2.me/submissions/0dc7eb87-809e-459c-be9a-dc1849026442

import Mathlib
import Definitions.Def_SGDKaczmarz_SGD_Setting

open MeasureTheory
open scoped NNReal ENNReal InnerProductSpace
open MeasureTheory
open scoped NNReal ENNReal InnerProductSpace

namespace SGDConvergenceProof

noncomputable def actualStep {I H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : I → H → ℝ) (γ : ℝ) (x : H) (i : I) : H :=
  x - γ • gradient (f i) x

def finiteRun {I H : Type*} (step : H → I → H) (x0 : H) :
    (k : ℕ) → (Fin k → I) → H
  | 0, _ => x0
  | k + 1, v => step (finiteRun step x0 k (fun j => v j.castSucc)) (v (Fin.last k))

noncomputable def finiteError {I H : Type*} [MeasurableSpace I] [NormedAddCommGroup H]
    (D : Measure I) (step : H → I → H) (x0 xstar : H) (k : ℕ) : ℝ≥0∞ :=
  ∫⁻ v, ENNReal.ofReal (‖finiteRun step x0 k v - xstar‖ ^ 2)
    ∂(Measure.pi (fun _ : Fin k => D))

def rate (γ μ supL : ℝ) : ℝ := 1 - 2 * γ * μ * (1 - γ * supL)

noncomputable def floorCoeff (γ μ supL : ℝ) : ℝ := γ / (μ * (1 - γ * supL))

end SGDConvergenceProof

open Set
open scoped NNReal InnerProductSpace

namespace SGDConvergenceProof

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

private lemma line_gradient {g : H → ℝ} (hd : Differentiable ℝ g) (x h : H) (t : ℝ) :
    HasDerivAt (fun s : ℝ => g (x + s • h)) ⟪gradient g (x + t • h), h⟫_ℝ t := by
  convert! ((hd _).hasFDerivAt.comp_hasDerivAt t
    (((hasDerivAt_id t).smul_const h).const_add x)) using 1
  simp

lemma gradient_support {g : H → ℝ} (hd : Differentiable ℝ g)
    (hc : ConvexOn ℝ univ g) (x y : H) :
    g x + ⟪gradient g x, y - x⟫_ℝ ≤ g y := by
  have hc' : ConvexOn ℝ univ (fun t : ℝ => g (x + t • (y - x))) := by
    simpa [Function.comp_def, AffineMap.lineMap_apply_module', add_comm] using
      hc.comp_affineMap (AffineMap.lineMap x y)
  have hd0 : HasDerivAt (fun t : ℝ => g (x + t • (y - x)))
      ⟪gradient g x, y - x⟫_ℝ 0 := by
    simpa only [zero_smul, add_zero] using line_gradient hd x (y - x) 0
  have hh := hc'.le_slope_of_hasDerivAt (mem_univ (0 : ℝ)) (mem_univ (1 : ℝ))
    zero_lt_one hd0
  have he : x + (y - x) = y := by abel
  simp only [slope, zero_smul, add_zero, one_smul, he, sub_zero, inv_one, one_smul, vsub_eq_sub] at hh
  linarith

lemma gradient_upper_model {g : H → ℝ} {L : ℝ≥0} (hd : Differentiable ℝ g)
    (hl : LipschitzWith L (gradient g)) (x h : H) :
    g (x + h) ≤ g x + ⟪gradient g x, h⟫_ℝ + (L : ℝ) / 2 * ‖h‖ ^ 2 := by
  let F : ℝ → ℝ := fun t => g (x + t • h) - t * ⟪gradient g x, h⟫_ℝ -
    (L : ℝ) / 2 * t ^ 2 * ‖h‖ ^ 2
  let F' : ℝ → ℝ := fun t => ⟪gradient g (x + t • h), h⟫_ℝ -
    ⟪gradient g x, h⟫_ℝ - (L : ℝ) * t * ‖h‖ ^ 2
  have hf (t : ℝ) : HasDerivAt F (F' t) t := by
    have hh := ((line_gradient hd x h t).sub ((hasDerivAt_id t).mul_const
      ⟪gradient g x, h⟫_ℝ)).sub
      ((((hasDerivAt_id t).pow 2).const_mul ((L : ℝ) / 2)).mul_const (‖h‖ ^ 2))
    convert! hh using 1
    dsimp [F']
    ring
  have ha : AntitoneOn F (Icc (0 : ℝ) 1) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
      (fun t _ => (hf t).continuousAt.continuousWithinAt)
      (fun t _ => (hf t).hasDerivWithinAt)
    intro t ht
    have ht0 : 0 ≤ t := (interior_subset ht).1
    have hn := hl.norm_sub_le (x + t • h) x
    have he : x + t • h - x = t • h := by abel
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0] at hn
    have hi := real_inner_le_norm (gradient g (x + t • h) - gradient g x) h
    have hm := mul_le_mul_of_nonneg_right hn (norm_nonneg h)
    rw [inner_sub_left] at hi
    dsimp [F']
    nlinarith
  have hh := ha (by simp) (by simp) (show (0 : ℝ) ≤ 1 by norm_num)
  dsimp [F] at hh
  simp only [one_smul, zero_smul, add_zero, one_mul, zero_mul, one_pow,
    mul_one, sub_zero] at hh
  linarith

lemma gradient_monotone {g : H → ℝ} (hd : Differentiable ℝ g)
    (hc : ConvexOn ℝ univ g) (x y : H) :
    0 ≤ ⟪x - y, gradient g x - gradient g y⟫_ℝ := by
  have h1 := gradient_support hd hc x y
  have h2 := gradient_support hd hc y x
  rw [← real_inner_comm (x - y) (gradient g x - gradient g y), inner_sub_left]
  have he : y - x = -(x - y) := by abel
  rw [he, inner_neg_right] at h1
  linarith

private lemma bregman {g : H → ℝ} {L : ℝ≥0} (hd : Differentiable ℝ g)
    (hl : LipschitzWith L (gradient g)) (hc : ConvexOn ℝ univ g)
    (hL : 0 < (L : ℝ)) (x y : H) :
    ‖gradient g x - gradient g y‖ ^ 2 ≤
      2 * (L : ℝ) * (g x - g y - ⟪gradient g y, x - y⟫_ℝ) := by
  let d := gradient g x - gradient g y
  let h := -((L : ℝ)⁻¹) • d
  have hu := gradient_upper_model hd hl x h
  have hs := gradient_support hd hc y (x + h)
  have he : x + h - y = (x - y) + h := by abel
  rw [he, inner_add_right] at hs
  have hi : ⟪d, h⟫_ℝ = ⟪gradient g x, h⟫_ℝ - ⟪gradient g y, h⟫_ℝ :=
    inner_sub_left _ _ _
  have hb : -(g x - g y - ⟪gradient g y, x - y⟫_ℝ) ≤
      ⟪d, h⟫_ℝ + (L : ℝ) / 2 * ‖h‖ ^ 2 := by linarith
  have hid : 2 * (L : ℝ) * (⟪d, h⟫_ℝ + (L : ℝ) / 2 * ‖h‖ ^ 2) = -‖d‖ ^ 2 := by
    dsimp [h]
    simp only [inner_smul_right, real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs,
      abs_neg, abs_inv, abs_of_pos hL, mul_pow]
    field_simp
    ring
  have hh := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 2 * (L : ℝ))
  rw [hid] at hh
  dsimp [d] at hh
  linarith

lemma cocoercive {g : H → ℝ} {L : ℝ≥0} (hd : Differentiable ℝ g)
    (hl : LipschitzWith L (gradient g)) (hc : ConvexOn ℝ univ g) (x y : H) :
    ‖gradient g x - gradient g y‖ ^ 2 ≤
      (L : ℝ) * ⟪x - y, gradient g x - gradient g y⟫_ℝ := by
  by_cases hL : (L : ℝ) = 0
  · have hn := hl.norm_sub_le x y
    rw [hL, zero_mul] at hn
    have hz : gradient g x - gradient g y = 0 := norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))
    simp [hz, hL]
  · have hp : 0 < (L : ℝ) := lt_of_le_of_ne L.coe_nonneg (Ne.symm hL)
    have h1 := bregman hd hl hc hp x y
    have h2 := bregman hd hl hc hp y x
    rw [norm_sub_rev] at h2
    have he : y - x = -(x - y) := by abel
    rw [he, inner_neg_right] at h2
    rw [← real_inner_comm (x - y) (gradient g x - gradient g y), inner_sub_left]
    nlinarith

end SGDConvergenceProof

open MeasureTheory Filter Set
open scoped NNReal ENNReal InnerProductSpace Topology
open SGDKaczmarz.SGD

namespace SGDConvergenceProof

variable {I : Type*} [MeasurableSpace I] (D : Measure I) [IsProbabilityMeasure D]

theorem supL_nonneg (L : I → ℝ≥0) (supL : ℝ)
    (hsup : ∀ᵐ i ∂D, (L i : ℝ) ≤ supL) : 0 ≤ supL := by
  obtain ⟨i, hi⟩ := hsup.exists
  exact (L i).coe_nonneg.trans hi

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

omit [SecondCountableTopology H] in
 theorem gradient_sq_integrable (f : I → H → ℝ) (L : I → ℝ≥0)
    (hlip : ∀ i, LipschitzWith (L i) (gradient (f i)))
    (supL : ℝ) (hsup : ∀ᵐ i ∂D, (L i : ℝ) ≤ supL)
    (hmeas : ∀ x, Measurable (fun i => gradient (f i) x))
    (xstar : H) (hres : residual D f xstar ≠ ⊤) (x : H) :
    Integrable (fun i => ‖gradient (f i) x‖ ^ 2) D := by
  have hstar : Integrable (fun i => ‖gradient (f i) xstar‖ ^ 2) D :=
    (lintegral_ofReal_ne_top_iff_integrable
      ((hmeas xstar).norm.pow_const 2).aestronglyMeasurable
      (ae_of_all D fun _ => sq_nonneg _)).mp hres
  have hs := supL_nonneg D L supL hsup
  refine ((hstar.const_mul 2).add (integrable_const (2 * (supL * ‖x - xstar‖) ^ 2))).mono'
    ((hmeas x).norm.pow_const 2).aestronglyMeasurable ?_
  filter_upwards [hsup] with i hi
  have hd : ‖gradient (f i) x - gradient (f i) xstar‖ ≤ supL * ‖x - xstar‖ :=
    (hlip i).norm_sub_le x xstar |>.trans (mul_le_mul_of_nonneg_right hi (norm_nonneg _))
  have hn := norm_le_norm_add_norm_sub' (gradient (f i) x) (gradient (f i) xstar)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  dsimp only [Pi.add_apply]
  nlinarith [sq_nonneg (‖gradient (f i) xstar‖ - supL * ‖x - xstar‖), norm_nonneg (gradient (f i) x), norm_nonneg (gradient (f i) xstar), mul_nonneg hs (norm_nonneg (x - xstar))]

theorem gradient_integrable (f : I → H → ℝ) (L : I → ℝ≥0)
    (hlip : ∀ i, LipschitzWith (L i) (gradient (f i)))
    (supL : ℝ) (hsup : ∀ᵐ i ∂D, (L i : ℝ) ≤ supL)
    (hmeas : ∀ x, Measurable (fun i => gradient (f i) x))
    (xstar : H) (hres : residual D f xstar ≠ ⊤) (x : H) :
    Integrable (fun i => gradient (f i) x) D := by
  have hi := gradient_sq_integrable D f L hlip supL hsup hmeas xstar hres x
  refine ((integrable_const (1 : ℝ)).add hi).mono' (hmeas x).aestronglyMeasurable ?_
  exact ae_of_all D fun i => by
    change ‖gradient (f i) x‖ ≤ 1 + ‖gradient (f i) x‖ ^ 2
    nlinarith [sq_nonneg (‖gradient (f i) x‖ - 1)]

omit [IsProbabilityMeasure D] [SecondCountableTopology H] in
 theorem residual_eq (f : I → H → ℝ) (xstar : H)
    (hmeas : ∀ x, Measurable (fun i => gradient (f i) x))
    (hres : residual D f xstar ≠ ⊤) :
    residual D f xstar = ENNReal.ofReal (∫ i, ‖gradient (f i) xstar‖ ^ 2 ∂D) := by
  have hi : Integrable (fun i => ‖gradient (f i) xstar‖ ^ 2) D :=
    (lintegral_ofReal_ne_top_iff_integrable
      ((hmeas xstar).norm.pow_const 2).aestronglyMeasurable
      (ae_of_all D fun _ => sq_nonneg _)).mp hres
  exact (ofReal_integral_eq_lintegral_ofReal hi (ae_of_all D fun _ => sq_nonneg _)).symm

theorem objective_hasGradient (f : I → H → ℝ) (L : I → ℝ≥0)
    (hdiff : ∀ i, Differentiable ℝ (f i))
    (hlip : ∀ i, LipschitzWith (L i) (gradient (f i)))
    (supL : ℝ) (hsup : ∀ᵐ i ∂D, (L i : ℝ) ≤ supL)
    (hint : ∀ x, Integrable (fun i => f i x) D)
    (hmeas : ∀ x, Measurable (fun i => gradient (f i) x))
    (xstar : H) (hres : residual D f xstar ≠ ⊤) (x : H) :
    HasGradientAt (objective D f) (∫ i, gradient (f i) x ∂D) x := by
  let A := (InnerProductSpace.toDual ℝ H).toContinuousLinearEquiv.toContinuousLinearMap
  have hg := gradient_integrable D f L hlip supL hsup hmeas xstar hres
  have hs := supL_nonneg D L supL hsup
  have hd : HasFDerivAt (fun y => ∫ i, f i y ∂D)
      (∫ i, A (gradient (f i) x) ∂D) x := by
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le
      (F' := fun y i => A (gradient (f i) y))
      (s := Metric.ball x 1)
      (bound := fun i => ‖gradient (f i) xstar‖ + supL * (‖x - xstar‖ + 1))
      (Metric.ball_mem_nhds x zero_lt_one)
    · exact Filter.Eventually.of_forall fun y => (hint y).aestronglyMeasurable
    · exact hint x
    · exact A.continuous.comp_aestronglyMeasurable (hmeas x).aestronglyMeasurable
    · filter_upwards [hsup] with i hi y hy
      have hd : ‖gradient (f i) y - gradient (f i) xstar‖ ≤ supL * ‖y - xstar‖ :=
        (hlip i).norm_sub_le y xstar |>.trans (mul_le_mul_of_nonneg_right hi (norm_nonneg _))
      have hy' : ‖y - x‖ < 1 := by simpa [dist_eq_norm] using hy
      have htri : ‖y - xstar‖ ≤ ‖y - x‖ + ‖x - xstar‖ := by
        simpa only [dist_eq_norm] using dist_triangle y x xstar
      change ‖(InnerProductSpace.toDual ℝ H) (gradient (f i) y)‖ ≤ _
      rw [(InnerProductSpace.toDual ℝ H).norm_map]
      have hn := norm_le_norm_add_norm_sub' (gradient (f i) y) (gradient (f i) xstar)
      nlinarith
    · exact (hg xstar).norm.add (integrable_const _)
    · exact ae_of_all D fun i y _ => (hdiff i y).hasGradientAt.hasFDerivAt
  rw [A.integral_comp_comm (hg x)] at hd
  exact hd

theorem objective_gradient (f : I → H → ℝ) (L : I → ℝ≥0)
    (hdiff : ∀ i, Differentiable ℝ (f i))
    (hlip : ∀ i, LipschitzWith (L i) (gradient (f i)))
    (supL : ℝ) (hsup : ∀ᵐ i ∂D, (L i : ℝ) ≤ supL)
    (hint : ∀ x, Integrable (fun i => f i x) D)
    (hmeas : ∀ x, Measurable (fun i => gradient (f i) x))
    (xstar : H) (hres : residual D f xstar ≠ ⊤) (x : H) :
    gradient (objective D f) x = ∫ i, gradient (f i) x ∂D :=
  (objective_hasGradient D f L hdiff hlip supL hsup hint hmeas xstar hres x).gradient

theorem objective_lipschitz (f : I → H → ℝ) (L : I → ℝ≥0)
    (hdiff : ∀ i, Differentiable ℝ (f i))
    (hlip : ∀ i, LipschitzWith (L i) (gradient (f i)))
    (supL : ℝ) (hsup : ∀ᵐ i ∂D, (L i : ℝ) ≤ supL)
    (hint : ∀ x, Integrable (fun i => f i x) D)
    (hmeas : ∀ x, Measurable (fun i => gradient (f i) x))
    (xstar : H) (hres : residual D f xstar ≠ ⊤) :
    LipschitzWith ⟨supL, supL_nonneg D L supL hsup⟩ (gradient (objective D f)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm]
  change ‖gradient (objective D f) x - gradient (objective D f) y‖ ≤ supL * ‖x - y‖
  rw [objective_gradient D f L hdiff hlip supL hsup hint hmeas xstar hres x,
    objective_gradient D f L hdiff hlip supL hsup hint hmeas xstar hres y,
    ← integral_sub (gradient_integrable D f L hlip supL hsup hmeas xstar hres x)
      (gradient_integrable D f L hlip supL hsup hmeas xstar hres y)]
  have h := norm_integral_le_of_norm_le_const (μ := D) (f := fun i => gradient (f i) x - gradient (f i) y)
    (C := supL * ‖x - y‖) (by
      filter_upwards [hsup] with i hi
      exact (hlip i).norm_sub_le x y |>.trans (mul_le_mul_of_nonneg_right hi (norm_nonneg _)))
  simpa using h

theorem objective_gradient_min (f : I → H → ℝ) (L : I → ℝ≥0)
    (hdiff : ∀ i, Differentiable ℝ (f i))
    (hlip : ∀ i, LipschitzWith (L i) (gradient (f i)))
    (supL : ℝ) (hsup : ∀ᵐ i ∂D, (L i : ℝ) ≤ supL)
    (hint : ∀ x, Integrable (fun i => f i x) D)
    (hmeas : ∀ x, Measurable (fun i => gradient (f i) x))
    (xstar : H) (hres : residual D f xstar ≠ ⊤)
    (hxstar : ∀ x, objective D f xstar ≤ objective D f x) :
    gradient (objective D f) xstar = 0 := by
  have hmin : IsLocalMin (objective D f) xstar := Filter.Eventually.of_forall hxstar
  have hg := objective_hasGradient D f L hdiff hlip supL hsup hint hmeas xstar hres xstar
  have hz := hmin.hasFDerivAt_eq_zero hg.hasFDerivAt
  rw [hg.gradient]
  exact (InnerProductSpace.toDual ℝ H).injective (by simpa using hz)

theorem mu_le_supL [Nontrivial H] (f : I → H → ℝ) (L : I → ℝ≥0)
    (hdiff : ∀ i, Differentiable ℝ (f i))
    (hlip : ∀ i, LipschitzWith (L i) (gradient (f i)))
    (supL : ℝ) (hsup : ∀ᵐ i ∂D, (L i : ℝ) ≤ supL)
    (hint : ∀ x, Integrable (fun i => f i x) D)
    (hmeas : ∀ x, Measurable (fun i => gradient (f i) x))
    (xstar : H) (hres : residual D f xstar ≠ ⊤) (μ : ℝ)
    (hF : ∀ x y, μ * ‖x - y‖ ^ 2 ≤
      ⟪x - y, gradient (objective D f) x - gradient (objective D f) y⟫_ℝ) :
    μ ≤ supL := by
  obtain ⟨v, hv⟩ := exists_ne (0 : H)
  have hn : 0 < ‖v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
  have h1 := hF v 0
  have h2 := real_inner_le_norm (v - 0) (gradient (objective D f) v - gradient (objective D f) 0)
  have h3 := (objective_lipschitz D f L hdiff hlip supL hsup hint hmeas xstar hres).norm_sub_le v 0
  change ‖gradient (objective D f) v - gradient (objective D f) 0‖ ≤ supL * ‖v - 0‖ at h3
  simp only [sub_zero] at h1 h2 h3
  have h4 := mul_le_mul_of_nonneg_left h3 (norm_nonneg v)
  nlinarith

omit [IsProbabilityMeasure D] in
 theorem actualStep_measurable (f : I → H → ℝ) (L : I → ℝ≥0)
    (hlip : ∀ i, LipschitzWith (L i) (gradient (f i)))
    (hmeas : ∀ x, Measurable (fun i => gradient (f i) x)) (γ : ℝ) :
    Measurable (Function.uncurry (actualStep f γ)) := by
  have hm : Measurable (Function.uncurry (fun x i => gradient (f i) x)) :=
    measurable_uncurry_of_continuous_of_measurable (fun i => (hlip i).continuous) hmeas
  exact measurable_fst.sub (hm.const_smul γ)

end SGDConvergenceProof

open MeasureTheory
open scoped ENNReal NNReal InnerProductSpace
open SGDKaczmarz.SGD

namespace SGDConvergenceProof

theorem expected_step_bound {I : Type*} [MeasurableSpace I] (D : Measure I)
    [IsProbabilityMeasure D] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    (f : I → H → ℝ) (L : I → ℝ≥0) (hdiff : ∀ i, Differentiable ℝ (f i))
    (hlip : ∀ i, LipschitzWith (L i) (gradient (f i)))
    (hconv : ∀ i, ConvexOn ℝ Set.univ (f i))
    (supL : ℝ) (hsup : ∀ᵐ i ∂D, (L i : ℝ) ≤ supL)
    (hint : ∀ x, Integrable (fun i => f i x) D)
    (hmeas : ∀ x, Measurable (fun i => gradient (f i) x))
    (μ : ℝ) (_hμ : 0 < μ)
    (hF : ∀ x y, μ * ‖x - y‖ ^ 2 ≤
      ⟪x - y, gradient (objective D f) x - gradient (objective D f) y⟫_ℝ)
    (xstar : H) (hxstar : ∀ x, objective D f xstar ≤ objective D f x)
    (γ : ℝ) (hγ : 0 < γ) (hγL : γ * supL < 1)
    (hres : residual D f xstar ≠ ⊤) (hq : 0 ≤ rate γ μ supL) (x : H) :
    (∫⁻ i, ENNReal.ofReal (‖actualStep f γ x i - xstar‖ ^ 2) ∂D) ≤
      ENNReal.ofReal (rate γ μ supL) * ENNReal.ofReal (‖x - xstar‖ ^ 2) +
        ENNReal.ofReal (2 * γ ^ 2) * residual D f xstar := by
  let d := x - xstar
  let R := ∫ i, ‖gradient (f i) xstar‖ ^ 2 ∂D
  have hR : 0 ≤ R := integral_nonneg fun _ => sq_nonneg _
  have hg := gradient_integrable D f L hlip supL hsup hmeas xstar hres
  have hg2 := gradient_sq_integrable D f L hlip supL hsup hmeas xstar hres
  have hmean := objective_gradient D f L hdiff hlip supL hsup hint hmeas xstar hres
  have hzero : (∫ i, gradient (f i) xstar ∂D) = 0 := by
    rw [← hmean xstar]
    exact objective_gradient_min D f L hdiff hlip supL hsup hint hmeas xstar hres hxstar
  have hip : Integrable (fun i => ⟪d, gradient (f i) x - gradient (f i) xstar⟫_ℝ) D :=
    Integrable.const_inner d ((hg x).sub (hg xstar))
  have hgb : (∫ i, ‖gradient (f i) x‖ ^ 2 ∂D) ≤
      2 * supL * ⟪d, gradient (objective D f) x⟫_ℝ + 2 * R := by
    have hi := integral_mono_ae (hg2 x) ((hip.const_mul (2 * supL)).add ((hg2 xstar).const_mul 2))
    have hp : ∀ᵐ i ∂D, ‖gradient (f i) x‖ ^ 2 ≤
        2 * supL * ⟪d, gradient (f i) x - gradient (f i) xstar⟫_ℝ +
          2 * ‖gradient (f i) xstar‖ ^ 2 := by
      filter_upwards [hsup] with i hi
      have hc := cocoercive (hdiff i) (hlip i) (hconv i) x xstar
      have hm := gradient_monotone (hdiff i) (hconv i) x xstar
      have hl := mul_le_mul_of_nonneg_right hi hm
      have hn := norm_le_norm_add_norm_sub' (gradient (f i) x) (gradient (f i) xstar)
      have hs := sq_nonneg (‖gradient (f i) x - gradient (f i) xstar‖ - ‖gradient (f i) xstar‖)
      dsimp [d]
      nlinarith [norm_nonneg (gradient (f i) x), norm_nonneg (gradient (f i) xstar),
        norm_nonneg (gradient (f i) x - gradient (f i) xstar)]
    have hb := hi hp
    simp only [Pi.add_apply] at hb
    rw [integral_add (hip.const_mul _) ((hg2 xstar).const_mul _), integral_const_mul,
      integral_const_mul, integral_inner (show Integrable (fun i => gradient (f i) x - gradient (f i) xstar) D from (hg x).sub (hg xstar)),
      integral_sub (hg x) (hg xstar), hzero, sub_zero, ← hmean x] at hb
    exact hb
  have heq : (fun i => ‖actualStep f γ x i - xstar‖ ^ 2) =
      (fun i => ‖d‖ ^ 2 - 2 * γ * ⟪d, gradient (f i) x⟫_ℝ +
        γ ^ 2 * ‖gradient (f i) x‖ ^ 2) := by
    funext i
    have he : actualStep f γ x i - xstar = d - γ • gradient (f i) x := by
      dsimp [actualStep, d]
      abel
    rw [he, norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  have hinner : Integrable (fun i => ⟪d, gradient (f i) x⟫_ℝ) D :=
    Integrable.const_inner d (hg x)
  have hpoly := ((integrable_const (‖d‖ ^ 2)).sub (hinner.const_mul (2 * γ))).add
    ((hg2 x).const_mul (γ ^ 2))
  have herr : Integrable (fun i => ‖actualStep f γ x i - xstar‖ ^ 2) D := by
    rw [heq]
    exact hpoly
  have hstrong : μ * ‖d‖ ^ 2 ≤ ⟪d, gradient (objective D f) x⟫_ℝ := by
    have hh := hF x xstar
    rw [objective_gradient_min D f L hdiff hlip supL hsup hint hmeas xstar hres hxstar,
      sub_zero] at hh
    exact hh
  have hreal : (∫ i, ‖actualStep f γ x i - xstar‖ ^ 2 ∂D) ≤
      rate γ μ supL * ‖d‖ ^ 2 + 2 * γ ^ 2 * R := by
    rw [heq, integral_add (show Integrable (fun i => ‖d‖ ^ 2 - 2 * γ * ⟪d, gradient (f i) x⟫_ℝ) D from (integrable_const _).sub (hinner.const_mul _)) ((hg2 x).const_mul _),
      integral_sub (integrable_const _) (hinner.const_mul _), integral_const,
      integral_const_mul, integral_const_mul, integral_inner (hg x), ← hmean x]
    simp only [probReal_univ, one_smul]
    have h1 := mul_le_mul_of_nonneg_left hgb (sq_nonneg γ)
    have h2 := mul_le_mul_of_nonneg_left hstrong
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hγ.le)
        (sub_nonneg.mpr hγL.le))
    dsimp [rate]
    nlinarith
  rw [← ofReal_integral_eq_lintegral_ofReal herr (ae_of_all D fun _ => sq_nonneg _)]
  refine (ENNReal.ofReal_le_ofReal hreal).trans_eq ?_
  rw [ENNReal.ofReal_add (mul_nonneg hq (sq_nonneg _)) (by positivity),
    ENNReal.ofReal_mul hq, ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * γ ^ 2),
    residual_eq D f xstar hmeas hres]

end SGDConvergenceProof

open MeasureTheory
open scoped NNReal ENNReal
open SGDKaczmarz.SGD

namespace SGDConvergenceProof

variable {I H : Type*} [MeasurableSpace I] [NormedAddCommGroup H]
  [MeasurableSpace H] [BorelSpace H]

omit [NormedAddCommGroup H] [BorelSpace H] in
 theorem finiteRun_measurable (step : H → I → H)
    (hstep : Measurable (Function.uncurry step)) (x0 : H) (k : ℕ) :
    Measurable (finiteRun step x0 k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    exact hstep.comp ((ih.comp (measurable_pi_lambda _ fun j => measurable_pi_apply j.castSucc)).prodMk
      (measurable_pi_apply (Fin.last k)))

omit [MeasurableSpace I] [MeasurableSpace H] [BorelSpace H] in
 theorem finiteRun_eq_iter [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : I → H → ℝ) (γ : ℝ) (x0 : H) (k : ℕ) (ω : ℕ → I) :
    finiteRun (actualStep f γ) x0 k (fun j => ω j.val) = sgdIter f γ x0 k ω := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simpa only [finiteRun, sgdIter, actualStep, Fin.val_castSucc, Fin.val_last] using
      (congrArg (fun x => x - γ • gradient (f (ω k)) x) ih)

variable (D : Measure I) [IsProbabilityMeasure D]

omit [MeasurableSpace H] [BorelSpace H] in
 theorem finiteError_zero (step : H → I → H) (x0 xstar : H) :
    finiteError D step x0 xstar 0 = ENNReal.ofReal (‖x0 - xstar‖ ^ 2) := by
  simp [finiteError, finiteRun]

theorem infinite_error_eq [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : I → H → ℝ) (γ : ℝ)
    (hstep : Measurable (Function.uncurry (actualStep f γ)))
    (x0 xstar : H) (k : ℕ) :
    (∫⁻ ω, ENNReal.ofReal (‖sgdIter f γ x0 k ω - xstar‖ ^ 2) ∂iidLaw D) =
      finiteError D (actualStep f γ) x0 xstar k := by
  let e : Fin k ≃ {j // j ∈ Finset.range k} :=
    { toFun := fun j => ⟨j.val, Finset.mem_range.mpr j.isLt⟩
      invFun := fun j => ⟨j.val, Finset.mem_range.mp j.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hr : MeasurePreserving (Finset.range k).restrict (iidLaw D)
      (Measure.pi (fun _ : {j // j ∈ Finset.range k} => D)) :=
    ⟨Finset.measurable_restrict _, Measure.infinitePi_map_restrict (fun _ : ℕ => D)⟩
  have hp := (measurePreserving_piCongrLeft (fun _ : Fin k => D) e.symm).comp hr
  have hm : Measurable (fun v => ENNReal.ofReal (‖finiteRun (actualStep f γ) x0 k v - xstar‖ ^ 2)) :=
    (((finiteRun_measurable _ hstep x0 k).sub_const xstar).norm.pow_const 2).ennreal_ofReal
  have hi := hp.lintegral_comp hm
  change (∫⁻ ω, ENNReal.ofReal (‖finiteRun (actualStep f γ) x0 k (fun j => ω j.val) - xstar‖ ^ 2)
    ∂iidLaw D) = _ at hi
  simpa only [finiteRun_eq_iter, finiteError] using hi

theorem finiteError_succ_le (step : H → I → H)
    (hstep : Measurable (Function.uncurry step)) (x0 xstar : H) (q b : ℝ≥0∞)
    (hbound : ∀ x, (∫⁻ i, ENNReal.ofReal (‖step x i - xstar‖ ^ 2) ∂D) ≤
      q * ENNReal.ofReal (‖x - xstar‖ ^ 2) + b) (k : ℕ) :
    finiteError D step x0 xstar (k + 1) ≤ q * finiteError D step x0 xstar k + b := by
  let F : I × (Fin k → I) → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (‖step (finiteRun step x0 k z.2) z.1 - xstar‖ ^ 2)
  have hF : Measurable F :=
    (((hstep.comp (((finiteRun_measurable step hstep x0 k).comp measurable_snd).prodMk
      measurable_fst)).sub_const xstar).norm.pow_const 2).ennreal_ofReal
  have hp := measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => D) (Fin.last k)
  have hi := hp.lintegral_comp hF
  have he : ∀ v : Fin (k + 1) → I,
      F (MeasurableEquiv.piFinSuccAbove (fun _ => I) (Fin.last k) v) =
        ENNReal.ofReal (‖finiteRun step x0 (k + 1) v - xstar‖ ^ 2) := by
    intro v
    change ENNReal.ofReal (‖step (finiteRun step x0 k (fun j => v ((Fin.last k).succAbove j)))
      (v (Fin.last k)) - xstar‖ ^ 2) = _
    simp only [Fin.succAbove_last, finiteRun]
  simp_rw [he] at hi
  change finiteError D step x0 xstar (k + 1) = ∫⁻ z, F z ∂D.prod (Measure.pi (fun _ : Fin k => D)) at hi
  rw [hi, lintegral_prod _ hF.aemeasurable, lintegral_lintegral_swap]
  · calc
      (∫⁻ v, ∫⁻ i, F (i, v) ∂D ∂Measure.pi (fun _ : Fin k => D)) ≤
          ∫⁻ v, q * ENNReal.ofReal (‖finiteRun step x0 k v - xstar‖ ^ 2) + b
            ∂Measure.pi (fun _ : Fin k => D) := lintegral_mono fun v => hbound _
      _ = _ := by
        have hm := (((finiteRun_measurable step hstep x0 k).sub_const xstar).norm.pow_const 2).ennreal_ofReal
        rw [lintegral_add_left (hm.const_mul q), lintegral_const_mul q hm]
        simp only [lintegral_const, measure_univ, mul_one, finiteError]
  · exact hF.aemeasurable

end SGDConvergenceProof

open scoped ENNReal

namespace SGDConvergenceProof

lemma rate_nonneg {γ μ supL : ℝ} (_hμ : 0 < μ) (hγ : 0 < γ)
    (hγL : γ * supL < 1) (hμL : μ ≤ supL) : 0 ≤ rate γ μ supL := by
  have hm : γ * μ ≤ γ * supL := mul_le_mul_of_nonneg_left hμL hγ.le
  have hp : 0 ≤ 1 - γ * supL := sub_nonneg.mpr hγL.le
  have hc := mul_le_mul_of_nonneg_right hm hp
  have hs := sq_nonneg (2 * (γ * supL) - 1)
  dsimp [rate]
  nlinarith

lemma floorCoeff_pos {γ μ supL : ℝ} (hμ : 0 < μ) (hγ : 0 < γ)
    (hγL : γ * supL < 1) : 0 < floorCoeff γ μ supL :=
  div_pos hγ (mul_pos hμ (sub_pos.mpr hγL))

lemma rate_floor_identity {γ μ supL : ℝ} (hμ : 0 < μ)
    (hγL : γ * supL < 1) :
    rate γ μ supL * floorCoeff γ μ supL + 2 * γ ^ 2 = floorCoeff γ μ supL := by
  unfold rate floorCoeff
  field_simp [hμ.ne', (sub_pos.mpr hγL).ne']
  ring

lemma affine_rate (a : ℕ → ℝ≥0∞) (q d c b : ℝ)
    (hq : 0 ≤ q) (_hd : 0 ≤ d) (hc : 0 ≤ c) (hb : 0 ≤ b)
    (hfix : q * c + b = c) (hzero : a 0 ≤ ENNReal.ofReal d)
    (hstep : ∀ k, a (k + 1) ≤ ENNReal.ofReal q * a k + ENNReal.ofReal b)
    (k : ℕ) : a k ≤ ENNReal.ofReal (q ^ k * d) + ENNReal.ofReal c := by
  induction k with
  | zero => simpa using hzero.trans (le_add_of_nonneg_right (zero_le))
  | succ k ih =>
    calc
      a (k + 1) ≤ ENNReal.ofReal q * a k + ENNReal.ofReal b := hstep k
      _ ≤ ENNReal.ofReal q * (ENNReal.ofReal (q ^ k * d) + ENNReal.ofReal c) +
          ENNReal.ofReal b := add_le_add (mul_le_mul' le_rfl ih) le_rfl
      _ = ENNReal.ofReal (q ^ (k + 1) * d) + ENNReal.ofReal c := by
        rw [mul_add, ← ENNReal.ofReal_mul hq, ← ENNReal.ofReal_mul hq, add_assoc,
          ← ENNReal.ofReal_add (mul_nonneg hq hc) hb, hfix]
        congr 2
        ring

end SGDConvergenceProof

open MeasureTheory
open scoped NNReal ENNReal InnerProductSpace

namespace SGDKaczmarz.SGD

/-- Theorem 2.1, (2.4), p. 4 (Needell–Srebro–Ward, arXiv:1310.5715v5): for `γ < 1/sup L` the SGD
iterates (2.2) satisfy
`E‖x_k − x⋆‖² ≤ [1 − 2γμ(1 − γ sup L)]^k ‖x_0 − x⋆‖² + γσ²/(μ(1 − γ sup L))`, the expectation being
over the i.i.d. sampling of `{i_k}`. -/
theorem theorem_2_1 {I : Type*} [MeasurableSpace I] (D : Measure I) [IsProbabilityMeasure D]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    (f : I → H → ℝ) (L : I → ℝ≥0)
    (hdiff : ∀ i, Differentiable ℝ (f i))
    (hlip : ∀ i, LipschitzWith (L i) (gradient (f i)))
    (hconv : ∀ i, ConvexOn ℝ Set.univ (f i))
    (supL : ℝ) (hsup : ∀ᵐ i ∂D, (L i : ℝ) ≤ supL)
    (hint : ∀ x, Integrable (fun i => f i x) D)
    (hmeas : ∀ x, Measurable (fun i => gradient (f i) x))
    (μ : ℝ) (hμ : 0 < μ)
    (hF : ∀ x y, μ * ‖x - y‖ ^ 2 ≤
      ⟪x - y, gradient (objective D f) x - gradient (objective D f) y⟫_ℝ)
    (xstar : H) (hxstar : ∀ x, objective D f xstar ≤ objective D f x)
    (γ : ℝ) (hγ : 0 < γ) (hγL : γ * supL < 1) (x0 : H) (k : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (‖sgdIter f γ x0 k ω - xstar‖ ^ 2) ∂(iidLaw D)
      ≤ ENNReal.ofReal ((1 - 2 * γ * μ * (1 - γ * supL)) ^ k * ‖x0 - xstar‖ ^ 2)
        + ENNReal.ofReal (γ / (μ * (1 - γ * supL))) * residual D f xstar := by
  classical
  have hc : 0 < γ / (μ * (1 - γ * supL)) :=
    SGDConvergenceProof.floorCoeff_pos hμ hγ hγL
  by_cases hres : residual D f xstar = ⊤
  · rw [hres, ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr hc))]
    simp
  cases subsingleton_or_nontrivial H with
  | inl h =>
    let := h
    have hz : ∀ ω, sgdIter f γ x0 k ω = xstar := fun _ => Subsingleton.elim _ _
    simp only [hz, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), ENNReal.ofReal_zero,
      MeasureTheory.lintegral_zero, zero_le]
  | inr h =>
    let := h
    have hμL := SGDConvergenceProof.mu_le_supL D f L hdiff hlip supL hsup hint hmeas xstar hres μ hF
    have hq := SGDConvergenceProof.rate_nonneg hμ hγ hγL hμL
    have hstep := SGDConvergenceProof.actualStep_measurable f L hlip hmeas γ
    let R : ℝ := ∫ i, ‖gradient (f i) xstar‖ ^ 2 ∂D
    have hR : 0 ≤ R := MeasureTheory.integral_nonneg fun _ => sq_nonneg _
    have hσ : residual D f xstar = ENNReal.ofReal R :=
      SGDConvergenceProof.residual_eq D f xstar hmeas hres
    have hrec : ∀ j,
        SGDConvergenceProof.finiteError D (SGDConvergenceProof.actualStep f γ) x0 xstar (j + 1) ≤
          ENNReal.ofReal (SGDConvergenceProof.rate γ μ supL) *
            SGDConvergenceProof.finiteError D (SGDConvergenceProof.actualStep f γ) x0 xstar j +
          ENNReal.ofReal (2 * γ ^ 2 * R) := by
      intro j
      have hb := SGDConvergenceProof.finiteError_succ_le D
        (SGDConvergenceProof.actualStep f γ) hstep x0 xstar
        (ENNReal.ofReal (SGDConvergenceProof.rate γ μ supL))
        (ENNReal.ofReal (2 * γ ^ 2) * residual D f xstar)
        (SGDConvergenceProof.expected_step_bound D f L hdiff hlip hconv supL hsup hint hmeas
          μ hμ hF xstar hxstar γ hγ hγL hres hq) j
      rw [hσ, ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * γ ^ 2)] at hb
      exact hb
    have hfix : SGDConvergenceProof.rate γ μ supL *
        (SGDConvergenceProof.floorCoeff γ μ supL * R) + 2 * γ ^ 2 * R =
        SGDConvergenceProof.floorCoeff γ μ supL * R := by
      have hi := congrArg (fun a : ℝ => a * R) (SGDConvergenceProof.rate_floor_identity hμ hγL)
      nlinarith only [hi]
    have hbound := SGDConvergenceProof.affine_rate
      (fun j => SGDConvergenceProof.finiteError D (SGDConvergenceProof.actualStep f γ) x0 xstar j)
      (SGDConvergenceProof.rate γ μ supL) (‖x0 - xstar‖ ^ 2)
      (SGDConvergenceProof.floorCoeff γ μ supL * R) (2 * γ ^ 2 * R)
      hq (sq_nonneg _) (mul_nonneg hc.le hR) (by positivity) hfix
      (le_of_eq (SGDConvergenceProof.finiteError_zero D _ x0 xstar)) hrec k
    rw [SGDConvergenceProof.infinite_error_eq D f γ hstep x0 xstar k, hσ,
      ← ENNReal.ofReal_mul hc.le]
    exact hbound

end SGDKaczmarz.SGD

open SGDKaczmarz.SGD

theorem solution {I : Type*} [MeasurableSpace I] (D : Measure I) [IsProbabilityMeasure D]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    (f : I → H → ℝ) (L : I → ℝ≥0)
    (hdiff : ∀ i, Differentiable ℝ (f i))
    (hlip : ∀ i, LipschitzWith (L i) (gradient (f i)))
    (hconv : ∀ i, ConvexOn ℝ Set.univ (f i))
    (supL : ℝ) (hsup : ∀ᵐ i ∂D, (L i : ℝ) ≤ supL)
    (hint : ∀ x, Integrable (fun i => f i x) D)
    (hmeas : ∀ x, Measurable (fun i => gradient (f i) x))
    (μ : ℝ) (hμ : 0 < μ)
    (hF : ∀ x y, μ * ‖x - y‖ ^ 2 ≤
      ⟪x - y, gradient (objective D f) x - gradient (objective D f) y⟫_ℝ)
    (xstar : H) (hxstar : ∀ x, objective D f xstar ≤ objective D f x)
    (γ : ℝ) (hγ : 0 < γ) (hγL : γ * supL < 1) (x0 : H) (k : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (‖sgdIter f γ x0 k ω - xstar‖ ^ 2) ∂(iidLaw D)
      ≤ ENNReal.ofReal ((1 - 2 * γ * μ * (1 - γ * supL)) ^ k * ‖x0 - xstar‖ ^ 2)
        + ENNReal.ofReal (γ / (μ * (1 - γ * supL))) * residual D f xstar := by
  exact SGDKaczmarz.SGD.theorem_2_1 D f L hdiff hlip hconv supL hsup hint hmeas μ hμ hF xstar hxstar γ hγ hγL x0 k
