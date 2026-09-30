-- Prove2me | solution 1 for RandomGradFree.Smooth.random_gradient_method_rate
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T00:44:55.030494+00:00
-- url     : https://prove2.me/submissions/9bae62cb-8ff0-44e7-aa81-07d2d1096a03

import Mathlib
import Definitions.Def_RandomGradFree_Smooth_IsRandomGradientRun

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace RG33

section analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma inner_grad (f : E → ℝ) (z w : E) : ⟪gradient f z, w⟫ = fderiv ℝ f z w := by
  simp [gradient, InnerProductSpace.toDual_symm_apply]

lemma line_deriv {f : E → ℝ} (hdiff : Differentiable ℝ f) (y w : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (y + s • w)) ⟪gradient f (y + t • w), w⟫ t := by
  have hl : HasDerivAt (fun s : ℝ => y + s • w) w t := by
    simpa using ((hasDerivAt_id t).smul_const w).const_add y
  have := (hdiff (y + t • w)).hasFDerivAt.comp_hasDerivAt t hl
  rw [inner_grad]
  exact this

lemma descent {f : E → ℝ} {L : ℝ} (hdiff : Differentiable ℝ f)
    (hgrad : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) (x y : E) :
    f y ≤ f x + ⟪gradient f x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2 := by
  set w := y - x
  let g : ℝ → ℝ := fun t => f (x + t • w) - t * ⟪gradient f x, w⟫ - L / 2 * t ^ 2 * ‖w‖ ^ 2
  have hg : ∀ t, HasDerivAt g (⟪gradient f (x + t • w), w⟫ - ⟪gradient f x, w⟫
      - L / 2 * (2 * t) * ‖w‖ ^ 2) t := by
    intro t
    have h1 := line_deriv hdiff x w t
    have h2 : HasDerivAt (fun s : ℝ => s * ⟪gradient f x, w⟫) ⟪gradient f x, w⟫ t := by
      simpa using (hasDerivAt_id t).mul_const ⟪gradient f x, w⟫
    have h3 : HasDerivAt (fun s : ℝ => L / 2 * s ^ 2 * ‖w‖ ^ 2) (L / 2 * (2 * t) * ‖w‖ ^ 2) t := by
      have := ((hasDerivAt_pow 2 t).const_mul (L / 2)).mul_const (‖w‖ ^ 2)
      simpa using this
    exact (h1.sub h2).sub h3
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope g _ (zero_lt_one' ℝ)
    (fun t _ => (hg t).continuousAt.continuousWithinAt) (fun t _ => hg t)
  have hle : ⟪gradient f (x + c • w), w⟫ - ⟪gradient f x, w⟫ - L / 2 * (2 * c) * ‖w‖ ^ 2 ≤ 0 := by
    have e1 : ⟪gradient f (x + c • w), w⟫ - ⟪gradient f x, w⟫ =
        ⟪gradient f (x + c • w) - gradient f x, w⟫ := by rw [inner_sub_left]
    have e2 := real_inner_le_norm (gradient f (x + c • w) - gradient f x) w
    have e3 := hgrad (x + c • w) x
    have e4 : ‖x + c • w - x‖ = c * ‖w‖ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hc.1]
    rw [e4] at e3
    have : ‖gradient f (x + c • w) - gradient f x‖ * ‖w‖ ≤ L * (c * ‖w‖) * ‖w‖ :=
      mul_le_mul_of_nonneg_right e3 (norm_nonneg _)
    nlinarith
  rw [hcd] at hle
  have : g 1 ≤ g 0 := by
    have := hle; simp only [sub_zero, div_one] at this; linarith
  simp only [g, one_smul, zero_smul, add_zero, one_mul, zero_mul, one_pow, sub_zero,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at this
  have hw : x + w = y := by simp [w]
  rw [hw] at this
  linarith

lemma convex_fo {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) (hdiff : Differentiable ℝ f) (x y : E) :
    f x + ⟪gradient f x, y - x⟫ ≤ f y := by
  set w := y - x
  have hφ : ConvexOn ℝ Set.univ (fun t : ℝ => f (x + t • w)) := by
    have := hf.comp_affineMap (AffineMap.lineMap x y)
    simp only [Set.preimage_univ] at this
    have e : (fun t : ℝ => f (x + t • w)) = f ∘ AffineMap.lineMap x y := by
      funext t
      simp [AffineMap.lineMap_apply, w, add_comm]
    rw [e]; exact this
  have h := hφ.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one
    (by simpa using line_deriv hdiff x w 0)
  rw [slope_def_field] at h
  simp only [zero_smul, add_zero, one_smul, sub_zero, div_one] at h
  have hw : x + w = y := by simp [w]
  rw [hw] at h
  rw [inner_grad]
  linarith

lemma grad_sq_le {f : E → ℝ} {L : ℝ} (hL : 0 < L) (hdiff : Differentiable ℝ f)
    (hgrad : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) {xstar : E}
    (hopt : ∀ y, f xstar ≤ f y) (x : E) :
    ‖gradient f x‖ ^ 2 ≤ 2 * L * (f x - f xstar) := by
  have h := descent hdiff hgrad x (x - (1 / L) • gradient f x)
  have h2 := hopt (x - (1 / L) • gradient f x)
  rw [sub_sub_cancel_left, inner_neg_right, real_inner_smul_right, norm_neg, norm_smul,
    real_inner_self_eq_norm_sq, Real.norm_eq_abs, abs_of_pos (by positivity)] at h
  have : L / 2 * (1 / L * ‖gradient f x‖) ^ 2 = 1 / (2 * L) * ‖gradient f x‖ ^ 2 := by
    field_simp
  rw [this] at h
  have h3 : 1 / L * ‖gradient f x‖ ^ 2 - 1 / (2 * L) * ‖gradient f x‖ ^ 2 ≤ f x - f xstar := by
    linarith
  have h4 : 1 / L * ‖gradient f x‖ ^ 2 - 1 / (2 * L) * ‖gradient f x‖ ^ 2 =
      ‖gradient f x‖ ^ 2 / (2 * L) := by field_simp; ring
  rw [h4, div_le_iff₀ (by positivity)] at h3
  linarith

lemma grad_star {f : E → ℝ} {L : ℝ} (hL : 0 < L) (hdiff : Differentiable ℝ f)
    (hgrad : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) {xstar : E}
    (hopt : ∀ y, f xstar ≤ f y) : gradient f xstar = 0 := by
  have := grad_sq_le hL hdiff hgrad hopt xstar
  rw [sub_self, mul_zero] at this
  have h0 : ‖gradient f xstar‖ = 0 := by nlinarith [norm_nonneg (gradient f xstar)]
  exact norm_eq_zero.mp h0

lemma grad_cont {f : E → ℝ} {L : ℝ} (hgrad : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) :
    Continuous (gradient f) := by
  have : LipschitzWith (Real.toNNReal L) (gradient f) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm, dist_eq_norm]
    refine (hgrad x y).trans (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal L) (norm_nonneg _))
  exact this.continuous

end analysis

/-! ### Polynomially bounded functions -/

section pb

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- polynomial growth -/
def PB (G : E → ℝ) : Prop := ∃ C : ℝ, ∃ k : ℕ, ∀ v, |G v| ≤ C * (1 + ‖v‖) ^ k

lemma PB.C_nonneg {G : E → ℝ} {C : ℝ} {k : ℕ} (h : ∀ v, |G v| ≤ C * (1 + ‖v‖) ^ k) : 0 ≤ C := by
  have := h 0
  simp only [norm_zero, add_zero, one_pow, mul_one] at this
  exact (abs_nonneg _).trans this

lemma PB.mono {G H : E → ℝ} (hH : PB H) (h : ∀ v, |G v| ≤ H v) : PB G := by
  obtain ⟨C, k, hC⟩ := hH
  exact ⟨C, k, fun v => (h v).trans ((le_abs_self _).trans (hC v))⟩

lemma PB.const (c : ℝ) : PB (fun _ : E => c) := ⟨|c|, 0, fun v => by simp⟩

lemma PB.inner (c : E) : PB (fun v : E => ⟪c, v⟫) :=
  ⟨‖c‖, 1, fun v => by
    rw [pow_one]
    exact (abs_real_inner_le_norm c v).trans
      (mul_le_mul_of_nonneg_left (by linarith [norm_nonneg v]) (norm_nonneg c))⟩

lemma PB.inner' (c : E) : PB (fun v : E => ⟪v, c⟫) :=
  ⟨‖c‖, 1, fun v => by
    show |⟪v, c⟫| ≤ _
    rw [pow_one, real_inner_comm]
    exact (abs_real_inner_le_norm c v).trans
      (mul_le_mul_of_nonneg_left (by linarith [norm_nonneg v]) (norm_nonneg c))⟩

lemma PB.normsq : PB (fun v : E => ‖v‖ ^ 2) :=
  ⟨1, 2, fun v => by
    rw [abs_of_nonneg (by positivity), one_mul]
    exact pow_le_pow_left₀ (norm_nonneg v) (by linarith) 2⟩

lemma PB.mul {G H : E → ℝ} (hG : PB G) (hH : PB H) : PB (fun v => G v * H v) := by
  obtain ⟨C1, k1, h1⟩ := hG
  obtain ⟨C2, k2, h2⟩ := hH
  refine ⟨C1 * C2, k1 + k2, fun v => ?_⟩
  rw [abs_mul, pow_add]
  calc |G v| * |H v| ≤ (C1 * (1 + ‖v‖) ^ k1) * (C2 * (1 + ‖v‖) ^ k2) :=
        mul_le_mul (h1 v) (h2 v) (abs_nonneg _) ((abs_nonneg _).trans (h1 v))
    _ = _ := by ring

lemma PB.add {G H : E → ℝ} (hG : PB G) (hH : PB H) : PB (fun v => G v + H v) := by
  obtain ⟨C1, k1, h1⟩ := hG
  obtain ⟨C2, k2, h2⟩ := hH
  have c1 := PB.C_nonneg h1
  have c2 := PB.C_nonneg h2
  refine ⟨C1 + C2, k1 + k2, fun v => ?_⟩
  have ht : (1 : ℝ) ≤ 1 + ‖v‖ := by linarith [norm_nonneg v]
  have e1 : (1 + ‖v‖) ^ k1 ≤ (1 + ‖v‖) ^ (k1 + k2) := pow_le_pow_right₀ ht (by omega)
  have e2 : (1 + ‖v‖) ^ k2 ≤ (1 + ‖v‖) ^ (k1 + k2) := pow_le_pow_right₀ ht (by omega)
  calc |G v + H v| ≤ |G v| + |H v| := abs_add_le _ _
    _ ≤ C1 * (1 + ‖v‖) ^ k1 + C2 * (1 + ‖v‖) ^ k2 := add_le_add (h1 v) (h2 v)
    _ ≤ C1 * (1 + ‖v‖) ^ (k1 + k2) + C2 * (1 + ‖v‖) ^ (k1 + k2) :=
        add_le_add (mul_le_mul_of_nonneg_left e1 c1) (mul_le_mul_of_nonneg_left e2 c2)
    _ = _ := by ring

lemma PB.pow {G : E → ℝ} (hG : PB G) (m : ℕ) : PB (fun v => G v ^ m) := by
  induction m with
  | zero => simpa using PB.const (E := E) 1
  | succ m ih => simpa [pow_succ] using ih.mul hG

lemma PB.abs {G : E → ℝ} (hG : PB G) : PB (fun v => |G v|) := by
  obtain ⟨C, k, h⟩ := hG
  exact ⟨C, k, fun v => by rw [abs_abs]; exact h v⟩

lemma PB.norm : PB (fun v : E => ‖v‖) :=
  ⟨1, 1, fun v => by rw [abs_of_nonneg (norm_nonneg v), one_mul, pow_one]; linarith⟩

lemma pow_le_two_pow (t : ℝ) (ht : 0 ≤ t) (k : ℕ) : (1 + t) ^ k ≤ 2 ^ k * (1 + t ^ k) := by
  have h1 : 1 + t ≤ 2 * max 1 t := by
    rcases le_total 1 t with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  calc (1 + t) ^ k ≤ (2 * max 1 t) ^ k := pow_le_pow_left₀ (by positivity) h1 k
    _ = 2 ^ k * (max 1 t) ^ k := mul_pow _ _ _
    _ ≤ 2 ^ k * (1 + t ^ k) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rcases le_total 1 t with h | h
        · rw [max_eq_right h]; linarith
        · rw [max_eq_left h, one_pow]; linarith [pow_nonneg ht k]

end pb

/-! ### Gaussian density on `Fin N → ℝ` (from 862efd33) -/

section dens

variable {N : ℕ}

/-- Unnormalised standard Gaussian weight. -/
noncomputable def gw (y : Fin N → ℝ) : ℝ := Real.exp (-(∑ i, y i ^ 2) / 2)

lemma prod_pdf (y : Fin N → ℝ) :
    ∏ i, gaussianPDFReal 0 1 (y i) = (Real.sqrt (2 * Real.pi))⁻¹ ^ N * gw y := by
  simp only [gaussianPDFReal, gw, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← Real.exp_sum, NNReal.coe_one, mul_one, sub_zero]
  congr 2
  simp only [neg_div, Finset.sum_neg_distrib, Finset.sum_div]

lemma pi_gauss_eq :
    Measure.pi (fun _ : Fin N => gaussianReal 0 1) =
      (volume : Measure (Fin N → ℝ)).withDensity
        (fun y => ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (y i))) := by
  apply Measure.pi_eq
  intro s hs
  have hbox : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
  rw [withDensity_apply _ hbox]
  simp_rw [gaussianReal_apply_eq_integral 0 one_ne_zero]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ =>
    setIntegral_nonneg (hs i) fun x _ => gaussianPDFReal_nonneg 0 1 x)]
  have hint : Integrable (fun y : Fin N → ℝ => ∏ i, gaussianPDFReal 0 1 (y i)) := by
    have := Integrable.fintype_prod (f := fun (_ : Fin N) (x : ℝ) => gaussianPDFReal 0 1 x)
      (μ := fun _ => volume) (fun _ => integrable_gaussianPDFReal 0 1)
    simpa [← volume_pi] using this
  rw [← ofReal_integral_eq_lintegral_ofReal hint.integrableOn
    (ae_of_all _ fun y => Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg 0 1 _)]
  congr 1
  rw [← integral_indicator hbox]
  have hind : (Set.univ.pi s).indicator (fun y : Fin N → ℝ => ∏ i, gaussianPDFReal 0 1 (y i)) =
      fun y => ∏ i, (s i).indicator (gaussianPDFReal 0 1) (y i) := by
    funext y
    by_cases hy : y ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hy]
      exact Finset.prod_congr rfl fun i _ => (Set.indicator_of_mem (hy i trivial) _).symm
    · rw [Set.indicator_of_notMem hy]
      obtain ⟨i, hi⟩ : ∃ i, y i ∉ s i := by simpa [Set.mem_pi] using hy
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm
  rw [hind, integral_fintype_prod_volume_eq_prod]
  simp_rw [integral_indicator (hs _)]

lemma meas_dens : Measurable (fun y : Fin N → ℝ => ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (y i))) :=
  ENNReal.measurable_ofReal.comp (Finset.measurable_prod _ fun i _ =>
    (measurable_gaussianPDFReal 0 1).comp (measurable_pi_apply i))

lemma integral_pi_gauss (g : (Fin N → ℝ) → ℝ) :
    ∫ y, g y ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1) =
      (Real.sqrt (2 * Real.pi))⁻¹ ^ N * ∫ y, gw y * g y := by
  rw [pi_gauss_eq, integral_withDensity_eq_integral_toReal_smul meas_dens
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top), ← integral_const_mul]
  congr 1
  funext y
  rw [ENNReal.toReal_ofReal (Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg 0 1 _),
    prod_pdf, smul_eq_mul, mul_assoc]

lemma intg_gw (F : (Fin N → ℝ) → ℝ)
    (hF : Integrable F (Measure.pi fun _ : Fin N => gaussianReal 0 1)) :
    Integrable (fun y => gw y * F y) volume := by
  rw [pi_gauss_eq, integrable_withDensity_iff_integrable_smul' meas_dens
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)] at hF
  have hc : (Real.sqrt (2 * Real.pi))⁻¹ ^ N ≠ 0 := by positivity
  refine (hF.const_mul ((Real.sqrt (2 * Real.pi))⁻¹ ^ N)⁻¹).congr (ae_of_all _ fun y => ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg 0 1 _),
    prod_pdf]
  field_simp

lemma hasLineDerivAt_gw (y v : Fin N → ℝ) :
    HasLineDerivAt ℝ gw (-(v ⬝ᵥ y) * gw y) y v := by
  have h1 : HasDerivAt (fun t : ℝ => ∑ i, (y i + t * v i) ^ 2) (∑ i, 2 * y i * v i) 0 := by
    apply HasDerivAt.fun_sum; intro i _
    have hl : HasDerivAt (fun t : ℝ => y i + t * v i) (v i) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v i)).const_add (y i)
    refine (hl.fun_pow 2).congr_deriv ?_
    simp
  have h3 : HasDerivAt (fun t : ℝ => gw (y + t • v))
      (Real.exp (-(∑ i, (y i + 0 * v i) ^ 2) / 2) * (-(∑ i, 2 * y i * v i) / 2)) 0 :=
    ((h1.neg).div_const 2).exp
  refine h3.congr_deriv ?_
  simp only [zero_mul, add_zero, gw, dotProduct]
  have : ∑ i, 2 * y i * v i = 2 * ∑ i, v i * y i := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [this]
  ring

end dens

/-! ### Stein's identity for the standard Gaussian on `E` -/

section stein

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

lemma intg_of_PB {G : E → ℝ} (hc : Continuous G) (hG : PB G) : Integrable G (stdGaussian E) := by
  obtain ⟨C, k, h⟩ := hG
  have hC := PB.C_nonneg h
  have hm : Integrable (fun v : E => ‖v‖ ^ k) (stdGaussian E) := by
    have := (IsGaussian.memLp_id (stdGaussian E) (k : ENNReal)
      (ENNReal.natCast_ne_top k)).integrable_norm_pow'
    simpa using this
  refine (((integrable_const (1 : ℝ)).add hm).const_mul (C * 2 ^ k)).mono'
    hc.aestronglyMeasurable (ae_of_all _ fun v => ?_)
  rw [Real.norm_eq_abs]
  calc |G v| ≤ C * (1 + ‖v‖) ^ k := h v
    _ ≤ C * (2 ^ k * (1 + ‖v‖ ^ k)) :=
        mul_le_mul_of_nonneg_left (pow_le_two_pow _ (norm_nonneg v) k) hC
    _ = C * 2 ^ k * (1 + ‖v‖ ^ k) := by ring

lemma stein {ψ ψ' : E → ℝ} (d : E) (hψc : Continuous ψ) (hψ'c : Continuous ψ') (hψ : PB ψ)
    (hψ' : PB ψ') (hder : ∀ v, HasLineDerivAt ℝ ψ (ψ' v) v d) :
    ∫ v, ⟪v, d⟫ * ψ v ∂stdGaussian E = ∫ v, ψ' v ∂stdGaussian E := by
  let b := stdOrthonormalBasis ℝ E
  let V : (Fin (Module.finrank ℝ E) → ℝ) → E := fun z => ∑ i, z i • b i
  let w : Fin (Module.finrank ℝ E) → ℝ := fun i => ⟪b i, d⟫
  have hV : Continuous V := by fun_prop
  have hγ : stdGaussian E =
      (Measure.pi fun _ : Fin (Module.finrank ℝ E) => gaussianReal 0 1).map V := rfl
  have hVd : ∀ z, w ⬝ᵥ z = ⟪V z, d⟫ := by
    intro z
    simp only [V, w, dotProduct, sum_inner, real_inner_smul_left, b]
    exact Finset.sum_congr rfl fun i _ => by rw [mul_comm]
  have hVadd : ∀ z (t : ℝ), V (z + t • w) = V z + t • d := by
    intro z t
    simp only [V, w, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul, Finset.sum_add_distrib,
      mul_smul, ← Finset.smul_sum, b, OrthonormalBasis.sum_repr']
  have e : ∀ G : E → ℝ, Continuous G → ∫ v, G v ∂stdGaussian E =
      (Real.sqrt (2 * Real.pi))⁻¹ ^ (Module.finrank ℝ E) * ∫ z, gw z * G (V z) := by
    intro G hG
    rw [hγ, integral_map hV.aemeasurable hG.aestronglyMeasurable, integral_pi_gauss]
  have t : ∀ G : E → ℝ, Continuous G → PB G → Integrable (fun z => gw z * G (V z)) volume := by
    intro G hc hp
    have := intg_of_PB hc hp
    rw [hγ, integrable_map_measure hc.aestronglyMeasurable hV.aemeasurable] at this
    exact intg_gw _ this
  have hc1 : Continuous (fun v => ⟪v, d⟫ * ψ v) := by fun_prop
  have hp1 : PB (fun v => ⟪v, d⟫ * ψ v) := (PB.inner' d).mul hψ
  rw [e _ hc1, e _ hψ'c]
  congr 1
  have hibp := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (μ := (volume : Measure (Fin (Module.finrank ℝ E) → ℝ))) (B := ContinuousLinearMap.mul ℝ ℝ)
    (f := gw) (f' := fun z => -(w ⬝ᵥ z) * gw z)
    (g := fun z => ψ (V z)) (g' := fun z => ψ' (V z)) (v := w) ?_ ?_ ?_
    (fun z _ => hasLineDerivAt_gw z w) (fun z _ => ?_)
  · simp only [ContinuousLinearMap.mul_apply'] at hibp
    rw [hibp, ← integral_neg]
    congr 1; funext z; rw [hVd]; ring
  · simp only [ContinuousLinearMap.mul_apply']
    exact (t _ hc1 hp1).neg.congr (ae_of_all _ fun z => by simp only [Pi.neg_apply]; rw [hVd]; ring)
  · simp only [ContinuousLinearMap.mul_apply']
    exact t _ hψ'c hψ'
  · simp only [ContinuousLinearMap.mul_apply']
    exact t _ hψc hψ
  · have := hder (V z)
    unfold HasLineDerivAt at this ⊢
    simp_rw [hVadd]
    exact this

lemma stein_lin_pow (c d : E) (m : ℕ) :
    ∫ v, ⟪v, d⟫ * (⟪c, v⟫ * (‖v‖ ^ 2) ^ m) ∂stdGaussian E =
      ∫ v, (⟪c, d⟫ * (‖v‖ ^ 2) ^ m + ⟪c, v⟫ * ((m : ℝ) * (‖v‖ ^ 2) ^ (m - 1) * (2 * ⟪v, d⟫)))
        ∂stdGaussian E := by
  apply stein d (by fun_prop) (by fun_prop) ((PB.inner c).mul (PB.normsq.pow m))
    (((PB.const _).mul (PB.normsq.pow m)).add ((PB.inner c).mul
      (((PB.const _).mul (PB.normsq.pow (m - 1))).mul ((PB.const 2).mul (PB.inner' d)))))
  intro v
  unfold HasLineDerivAt
  have h1 : HasDerivAt (fun t : ℝ => ⟪c, v + t • d⟫) ⟪c, d⟫ 0 := by
    have : (fun t : ℝ => ⟪c, v + t • d⟫) = fun t => ⟪c, v⟫ + t * ⟪c, d⟫ := by
      funext t; rw [inner_add_right, real_inner_smul_right]
    rw [this]; simpa using ((hasDerivAt_id (0 : ℝ)).mul_const ⟪c, d⟫).const_add ⟪c, v⟫
  have h2 : HasDerivAt (fun t : ℝ => ‖v + t • d‖ ^ 2) (2 * ⟪v, d⟫) 0 := by
    have : (fun t : ℝ => ‖v + t • d‖ ^ 2) = fun t => ‖v‖ ^ 2 + 2 * (t * ⟪v, d⟫) + t ^ 2 * ‖d‖ ^ 2 := by
      funext t
      rw [norm_add_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    rw [this]
    have key : HasDerivAt (fun t : ℝ => ‖v‖ ^ 2 + 2 * (t * ⟪v, d⟫) + t ^ 2 * ‖d‖ ^ 2)
        (2 * (1 * ⟪v, d⟫) + ((2 : ℕ) : ℝ) * 0 ^ (2 - 1) * ‖d‖ ^ 2) 0 :=
      ((((hasDerivAt_id (0 : ℝ)).mul_const ⟪v, d⟫).const_mul 2).const_add (‖v‖ ^ 2)).add
        ((hasDerivAt_pow 2 (0 : ℝ)).mul_const (‖d‖ ^ 2))
    exact key.congr_deriv (by norm_num)
  have key : HasDerivAt (fun t : ℝ => ⟪c, v + t • d⟫ * (‖v + t • d‖ ^ 2) ^ m)
      (⟪c, d⟫ * (‖v + (0 : ℝ) • d‖ ^ 2) ^ m + ⟪c, v + (0 : ℝ) • d⟫ *
        ((m : ℝ) * (‖v + (0 : ℝ) • d‖ ^ 2) ^ (m - 1) * (2 * ⟪v, d⟫))) 0 := h1.mul (h2.fun_pow m)
  refine key.congr_deriv ?_
  simp only [zero_smul, add_zero]

end stein

section moments

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

lemma mom_succ (m : ℕ) :
    ∫ v, (‖v‖ ^ 2) ^ (m + 1) ∂stdGaussian E =
      ((Module.finrank ℝ E : ℝ) + 2 * m) * ∫ v, (‖v‖ ^ 2) ^ m ∂stdGaussian E := by
  let b := stdOrthonormalBasis ℝ E
  have hsum : ∀ v : E, ∑ i, ⟪b i, v⟫ ^ 2 = ‖v‖ ^ 2 := b.sum_sq_inner_right
  have hbb : ∀ i, ⟪b i, b i⟫ = 1 := fun i => by
    rw [real_inner_self_eq_norm_sq, b.orthonormal.1 i]; norm_num
  have hI : ∀ i, Integrable (fun v : E => ⟪v, b i⟫ * (⟪b i, v⟫ * (‖v‖ ^ 2) ^ m))
      (stdGaussian E) := fun i =>
    intg_of_PB (by fun_prop) ((PB.inner' _).mul ((PB.inner _).mul (PB.normsq.pow m)))
  have hJ : ∀ i, Integrable (fun v : E => ⟪b i, b i⟫ * (‖v‖ ^ 2) ^ m +
      ⟪b i, v⟫ * ((m : ℝ) * (‖v‖ ^ 2) ^ (m - 1) * (2 * ⟪v, b i⟫))) (stdGaussian E) := fun i =>
    intg_of_PB (by fun_prop) (((PB.const _).mul (PB.normsq.pow m)).add ((PB.inner _).mul
      (((PB.const _).mul (PB.normsq.pow (m - 1))).mul ((PB.const 2).mul (PB.inner' _)))))
  calc ∫ v, (‖v‖ ^ 2) ^ (m + 1) ∂stdGaussian E
      = ∫ v, ∑ i, ⟪v, b i⟫ * (⟪b i, v⟫ * (‖v‖ ^ 2) ^ m) ∂stdGaussian E := by
        congr 1; funext v
        have : ∀ i, ⟪v, b i⟫ * (⟪b i, v⟫ * (‖v‖ ^ 2) ^ m) = ⟪b i, v⟫ ^ 2 * (‖v‖ ^ 2) ^ m := by
          intro i; rw [real_inner_comm (b i) v]; ring
        rw [Finset.sum_congr rfl (fun i _ => this i), ← Finset.sum_mul, hsum, pow_succ]; ring
    _ = ∑ i, ∫ v, ⟪v, b i⟫ * (⟪b i, v⟫ * (‖v‖ ^ 2) ^ m) ∂stdGaussian E :=
        integral_finsetSum _ (fun i _ => hI i)
    _ = ∑ i, ∫ v, (⟪b i, b i⟫ * (‖v‖ ^ 2) ^ m +
          ⟪b i, v⟫ * ((m : ℝ) * (‖v‖ ^ 2) ^ (m - 1) * (2 * ⟪v, b i⟫))) ∂stdGaussian E :=
        Finset.sum_congr rfl fun i _ => stein_lin_pow _ _ m
    _ = ∫ v, ∑ i, (⟪b i, b i⟫ * (‖v‖ ^ 2) ^ m +
          ⟪b i, v⟫ * ((m : ℝ) * (‖v‖ ^ 2) ^ (m - 1) * (2 * ⟪v, b i⟫))) ∂stdGaussian E :=
        (integral_finsetSum _ (fun i _ => hJ i)).symm
    _ = ∫ v, ((Module.finrank ℝ E : ℝ) + 2 * m) * (‖v‖ ^ 2) ^ m ∂stdGaussian E := by
        congr 1; funext v
        have : ∀ i, ⟪b i, b i⟫ * (‖v‖ ^ 2) ^ m +
            ⟪b i, v⟫ * ((m : ℝ) * (‖v‖ ^ 2) ^ (m - 1) * (2 * ⟪v, b i⟫)) =
            (‖v‖ ^ 2) ^ m + 2 * m * (‖v‖ ^ 2) ^ (m - 1) * ⟪b i, v⟫ ^ 2 := by
          intro i; rw [hbb, real_inner_comm (b i) v]; ring
        rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_add_distrib, ← Finset.mul_sum,
          hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rcases m with _ | k
        · simp
        · simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]; ring
    _ = _ := integral_const_mul _ _

lemma mom2 : ∫ v, ‖v‖ ^ 2 ∂stdGaussian E = (Module.finrank ℝ E : ℝ) := by
  have := mom_succ (E := E) 0
  simpa using this

lemma mom6 : ∫ v, (‖v‖ ^ 2) ^ 3 ∂stdGaussian E =
    ((Module.finrank ℝ E : ℝ) + 4) * ((Module.finrank ℝ E : ℝ) + 2) * (Module.finrank ℝ E : ℝ) := by
  rw [mom_succ 2, mom_succ 1]
  simp only [pow_one]
  rw [mom2]
  push_cast; ring

lemma mom_a2 (a : E) : ∫ v, ⟪a, v⟫ ^ 2 ∂stdGaussian E = ‖a‖ ^ 2 := by
  calc ∫ v, ⟪a, v⟫ ^ 2 ∂stdGaussian E
      = ∫ v, ⟪v, a⟫ * (⟪a, v⟫ * (‖v‖ ^ 2) ^ 0) ∂stdGaussian E := by
        congr 1; funext v; rw [real_inner_comm a v]; ring
    _ = ∫ v, (⟪a, a⟫ * (‖v‖ ^ 2) ^ 0 +
          ⟪a, v⟫ * (((0 : ℕ) : ℝ) * (‖v‖ ^ 2) ^ (0 - 1) * (2 * ⟪v, a⟫))) ∂stdGaussian E :=
        stein_lin_pow a a 0
    _ = ‖a‖ ^ 2 := by simp

lemma mom_a2n2 (a : E) : ∫ v, ⟪a, v⟫ ^ 2 * ‖v‖ ^ 2 ∂stdGaussian E =
    ((Module.finrank ℝ E : ℝ) + 2) * ‖a‖ ^ 2 := by
  calc ∫ v, ⟪a, v⟫ ^ 2 * ‖v‖ ^ 2 ∂stdGaussian E
      = ∫ v, ⟪v, a⟫ * (⟪a, v⟫ * (‖v‖ ^ 2) ^ 1) ∂stdGaussian E := by
        congr 1; funext v; rw [real_inner_comm a v]; ring
    _ = ∫ v, (⟪a, a⟫ * (‖v‖ ^ 2) ^ 1 +
          ⟪a, v⟫ * (((1 : ℕ) : ℝ) * (‖v‖ ^ 2) ^ (1 - 1) * (2 * ⟪v, a⟫))) ∂stdGaussian E :=
        stein_lin_pow a a 1
    _ = ∫ v, (‖a‖ ^ 2 * ‖v‖ ^ 2 + 2 * ⟪a, v⟫ ^ 2) ∂stdGaussian E := by
        congr 1; funext v; rw [real_inner_self_eq_norm_sq, real_inner_comm a v]; simp; ring
    _ = ((Module.finrank ℝ E : ℝ) + 2) * ‖a‖ ^ 2 := by
        rw [integral_add (intg_of_PB (by fun_prop) ((PB.const _).mul PB.normsq))
          (intg_of_PB (by fun_prop) ((PB.const _).mul ((PB.inner a).pow 2))),
          integral_const_mul, integral_const_mul, mom2, mom_a2]
        ring

end moments

/-! ### The oracle coefficient and the one-step bound -/

section core

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- scalar coefficient of the oracle -/
noncomputable def coef (f : E → ℝ) (μ : ℝ) (y v : E) : ℝ :=
  if μ = 0 then ⟪gradient f y, v⟫ else (f (y + μ • v) - f y) / μ

variable {f : E → ℝ} {L μ : ℝ}

lemma coef_bounds (hdiff : Differentiable ℝ f)
    (hgrad : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hf : ConvexOn ℝ Set.univ f) (hμ : 0 ≤ μ) (y v : E) :
    ⟪gradient f y, v⟫ ≤ coef f μ y v ∧
      coef f μ y v ≤ ⟪gradient f y, v⟫ + L * μ / 2 * ‖v‖ ^ 2 := by
  unfold coef
  split_ifs with h0
  · subst h0; simp
  · have hμp : 0 < μ := lt_of_le_of_ne hμ (Ne.symm h0)
    have h1 := convex_fo hf hdiff y (y + μ • v)
    have h2 := descent hdiff hgrad y (y + μ • v)
    rw [add_sub_cancel_left, real_inner_smul_right] at h1 h2
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hμp] at h2
    constructor
    · rw [le_div_iff₀ hμp]; linarith
    · rw [div_le_iff₀ hμp]
      have e : (⟪gradient f y, v⟫ + L * μ / 2 * ‖v‖ ^ 2) * μ =
          μ * ⟪gradient f y, v⟫ + L / 2 * (μ * ‖v‖) ^ 2 := by ring
      rw [e]; linarith

lemma coef_cont_joint (hdiff : Differentiable ℝ f)
    (hgrad : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) :
    Continuous (fun p : E × E => coef f μ p.1 p.2) := by
  unfold coef
  split_ifs with h0
  · exact ((grad_cont hgrad).comp continuous_fst).inner continuous_snd
  · have hc := hdiff.continuous
    fun_prop

lemma coef_cont (hdiff : Differentiable ℝ f)
    (hgrad : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) (y : E) :
    Continuous (coef f μ y) :=
  (coef_cont_joint (μ := μ) hdiff hgrad).comp (continuous_const.prodMk continuous_id)

lemma coef_PB (hL : 0 < L) (hdiff : Differentiable ℝ f)
    (hgrad : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hf : ConvexOn ℝ Set.univ f) (hμ : 0 ≤ μ) (y : E) : PB (coef f μ y) :=
  ((PB.inner (gradient f y)).abs.add ((PB.const (L * μ / 2)).mul PB.normsq)).mono fun v => by
    show |coef f μ y v| ≤ |⟪gradient f y, v⟫| + L * μ / 2 * ‖v‖ ^ 2
    obtain ⟨h1, h2⟩ := coef_bounds hdiff hgrad hf hμ y v
    have hnn : 0 ≤ L * μ / 2 * ‖v‖ ^ 2 := by positivity
    rw [abs_le]
    constructor
    · linarith [neg_abs_le ⟪gradient f y, v⟫]
    · linarith [le_abs_self ⟪gradient f y, v⟫]

lemma coef_deriv (hdiff : Differentiable ℝ f) (y d v : E) :
    HasLineDerivAt ℝ (coef f μ y) ⟪gradient f (y + μ • v), d⟫ v d := by
  unfold HasLineDerivAt coef
  split_ifs with h0
  · subst h0
    simp only [zero_smul, add_zero]
    have : (fun t : ℝ => ⟪gradient f y, v + t • d⟫) =
        fun t => ⟪gradient f y, v⟫ + t * ⟪gradient f y, d⟫ := by
      funext t; rw [inner_add_right, real_inner_smul_right]
    rw [this]
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const ⟪gradient f y, d⟫).const_add ⟪gradient f y, v⟫
  · have hl := line_deriv hdiff (y + μ • v) (μ • d) 0
    have e : (fun t : ℝ => (f (y + μ • (v + t • d)) - f y) / μ) =
        fun t => (f ((y + μ • v) + t • (μ • d)) - f y) / μ := by
      funext t; congr 3; module
    rw [e]
    refine ((hl.sub_const (f y)).div_const μ).congr_deriv ?_
    rw [zero_smul, add_zero, real_inner_smul_right]
    field_simp

lemma I1 (hL : 0 < L) (hdiff : Differentiable ℝ f)
    (hgrad : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hf : ConvexOn ℝ Set.univ f) {xstar : E} (hμ : 0 ≤ μ) (x : E) :
    f x - f xstar - L * μ ^ 2 / 2 * (Module.finrank ℝ E : ℝ) ≤
      ∫ v, ⟪v, x - xstar⟫ * coef f μ x v ∂stdGaussian E := by
  have hψ'c : Continuous (fun v => ⟪gradient f (x + μ • v), x - xstar⟫) :=
    ((grad_cont hgrad).comp (by fun_prop)).inner continuous_const
  have hψ'p : PB (fun v => ⟪gradient f (x + μ • v), x - xstar⟫) :=
    ((PB.const (‖gradient f x‖ * ‖x - xstar‖)).add
      ((PB.const (L * μ * ‖x - xstar‖)).mul PB.norm)).mono fun v => by
      show |⟪gradient f (x + μ • v), x - xstar⟫| ≤
        ‖gradient f x‖ * ‖x - xstar‖ + L * μ * ‖x - xstar‖ * ‖v‖
      have h1 := abs_real_inner_le_norm (gradient f (x + μ • v)) (x - xstar)
      have h2 := hgrad (x + μ • v) x
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hμ] at h2
      have h3 : ‖gradient f (x + μ • v)‖ ≤ ‖gradient f x‖ + L * (μ * ‖v‖) := by
        calc ‖gradient f (x + μ • v)‖
            = ‖(gradient f (x + μ • v) - gradient f x) + gradient f x‖ := by rw [sub_add_cancel]
          _ ≤ ‖gradient f (x + μ • v) - gradient f x‖ + ‖gradient f x‖ := norm_add_le _ _
          _ ≤ _ := by linarith
      have h4 := mul_le_mul_of_nonneg_right h3 (norm_nonneg (x - xstar))
      nlinarith
  rw [stein (x - xstar) (coef_cont hdiff hgrad x) hψ'c (coef_PB hL hdiff hgrad hf hμ x) hψ'p
    (fun v => coef_deriv hdiff x (x - xstar) v)]
  have hlow : ∀ v, f x - f xstar - L * μ ^ 2 / 2 * ‖v‖ ^ 2 ≤
      ⟪gradient f (x + μ • v), x - xstar⟫ := by
    intro v
    have h1 := convex_fo hf hdiff (x + μ • v) xstar
    have h2 := descent hdiff hgrad (x + μ • v) x
    have e1 : ‖x - (x + μ • v)‖ = μ * ‖v‖ := by
      rw [sub_add_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hμ]
    have e2 : ⟪gradient f (x + μ • v), x - xstar⟫ = ⟪gradient f (x + μ • v), x - (x + μ • v)⟫ +
        ⟪gradient f (x + μ • v), (x + μ • v) - xstar⟫ := by
      rw [← inner_add_right, sub_add_sub_cancel]
    have e3 : ⟪gradient f (x + μ • v), xstar - (x + μ • v)⟫ =
        -⟪gradient f (x + μ • v), (x + μ • v) - xstar⟫ := by
      rw [← inner_neg_right, neg_sub]
    rw [e1, mul_pow] at h2
    rw [e3] at h1
    rw [e2]
    linarith
  have hn2 : Integrable (fun v : E => ‖v‖ ^ 2) (stdGaussian E) :=
    intg_of_PB (by fun_prop) PB.normsq
  have hc : Integrable (fun v : E => f x - f xstar - L * μ ^ 2 / 2 * ‖v‖ ^ 2) (stdGaussian E) :=
    (integrable_const _).sub (hn2.const_mul _)
  calc f x - f xstar - L * μ ^ 2 / 2 * (Module.finrank ℝ E : ℝ)
      = ∫ v, (f x - f xstar - L * μ ^ 2 / 2 * ‖v‖ ^ 2) ∂stdGaussian E := by
        rw [integral_sub (integrable_const _) (hn2.const_mul _), integral_const, integral_const_mul,
          mom2]
        simp
    _ ≤ _ := integral_mono hc (intg_of_PB hψ'c hψ'p) hlow

lemma I2 (hL : 0 < L) (hdiff : Differentiable ℝ f)
    (hgrad : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hf : ConvexOn ℝ Set.univ f) (hμ : 0 ≤ μ) (x : E) :
    ∫ v, coef f μ x v ^ 2 * ‖v‖ ^ 2 ∂stdGaussian E ≤
      2 * ((Module.finrank ℝ E : ℝ) + 2) * ‖gradient f x‖ ^ 2 +
        L ^ 2 * μ ^ 2 / 2 * (((Module.finrank ℝ E : ℝ) + 4) * ((Module.finrank ℝ E : ℝ) + 2) *
          (Module.finrank ℝ E : ℝ)) := by
  have hc := coef_cont (μ := μ) hdiff hgrad x
  have hint1 : Integrable (fun v => coef f μ x v ^ 2 * ‖v‖ ^ 2) (stdGaussian E) :=
    intg_of_PB (by fun_prop) (((coef_PB hL hdiff hgrad hf hμ x).pow 2).mul PB.normsq)
  have hA : Integrable (fun v : E => ⟪gradient f x, v⟫ ^ 2 * ‖v‖ ^ 2) (stdGaussian E) :=
    intg_of_PB (by fun_prop) (((PB.inner _).pow 2).mul PB.normsq)
  have hB : Integrable (fun v : E => (‖v‖ ^ 2) ^ 3) (stdGaussian E) :=
    intg_of_PB (by fun_prop) (PB.normsq.pow 3)
  calc ∫ v, coef f μ x v ^ 2 * ‖v‖ ^ 2 ∂stdGaussian E
      ≤ ∫ v, (2 * (⟪gradient f x, v⟫ ^ 2 * ‖v‖ ^ 2) + L ^ 2 * μ ^ 2 / 2 * (‖v‖ ^ 2) ^ 3)
          ∂stdGaussian E := by
        refine integral_mono hint1 ((hA.const_mul 2).add (hB.const_mul _)) (fun v => ?_)
        obtain ⟨h1, h2⟩ := coef_bounds hdiff hgrad hf hμ x v
        have hr : 0 ≤ ‖v‖ ^ 2 := by positivity
        have hρ : (coef f μ x v - ⟪gradient f x, v⟫) ^ 2 ≤ (L * μ / 2 * ‖v‖ ^ 2) ^ 2 :=
          pow_le_pow_left₀ (by linarith) (by linarith) 2
        have hc2 : coef f μ x v ^ 2 ≤ 2 * ⟪gradient f x, v⟫ ^ 2 +
            2 * (coef f μ x v - ⟪gradient f x, v⟫) ^ 2 := by
          nlinarith [sq_nonneg (coef f μ x v - 2 * ⟪gradient f x, v⟫)]
        calc coef f μ x v ^ 2 * ‖v‖ ^ 2
            ≤ (2 * ⟪gradient f x, v⟫ ^ 2 + 2 * (L * μ / 2 * ‖v‖ ^ 2) ^ 2) * ‖v‖ ^ 2 :=
              mul_le_mul_of_nonneg_right (by linarith) hr
          _ = _ := by ring
    _ = _ := by
        rw [integral_add (hA.const_mul 2) (hB.const_mul _), integral_const_mul, integral_const_mul,
          mom_a2n2, mom6]
        ring

lemma step_bound (hL : 0 < L) (hdiff : Differentiable ℝ f)
    (hgrad : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hf : ConvexOn ℝ Set.univ f) {xstar : E} (hopt : ∀ y, f xstar ≤ f y) (hμ : 0 ≤ μ)
    {h : ℝ} (hh : h = 1 / (4 * ((Module.finrank ℝ E : ℝ) + 4) * L)) (x : E) :
    Integrable (fun v => ‖x - h • (coef f μ x v • v) - xstar‖ ^ 2) (stdGaussian E) ∧
    ∫ v, ‖x - h • (coef f μ x v • v) - xstar‖ ^ 2 ∂stdGaussian E ≤
      ‖x - xstar‖ ^ 2 - h * (f x - f xstar) +
        h * μ ^ 2 * L * (9 * ((Module.finrank ℝ E : ℝ) + 4) ^ 2 / 25) := by
  set n : ℝ := (Module.finrank ℝ E : ℝ) with hn
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hc := coef_cont (μ := μ) hdiff hgrad x
  have hpt : ∀ v, ‖x - h • (coef f μ x v • v) - xstar‖ ^ 2 = ‖x - xstar‖ ^ 2 -
      2 * h * (⟪v, x - xstar⟫ * coef f μ x v) + h ^ 2 * (coef f μ x v ^ 2 * ‖v‖ ^ 2) := by
    intro v
    have : x - h • (coef f μ x v • v) - xstar = (x - xstar) - (h * coef f μ x v) • v := by
      rw [smul_smul]; abel
    rw [this, norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs,
      sq_abs, real_inner_comm]
    ring
  have hi1 : Integrable (fun v => ⟪v, x - xstar⟫ * coef f μ x v) (stdGaussian E) :=
    intg_of_PB (by fun_prop) ((PB.inner' _).mul (coef_PB hL hdiff hgrad hf hμ x))
  have hi2 : Integrable (fun v => coef f μ x v ^ 2 * ‖v‖ ^ 2) (stdGaussian E) :=
    intg_of_PB (by fun_prop) (((coef_PB hL hdiff hgrad hf hμ x).pow 2).mul PB.normsq)
  have hint : Integrable (fun v => ‖x - xstar‖ ^ 2 -
      2 * h * (⟪v, x - xstar⟫ * coef f μ x v) + h ^ 2 * (coef f μ x v ^ 2 * ‖v‖ ^ 2))
      (stdGaussian E) :=
    ((integrable_const _).sub (hi1.const_mul _)).add (hi2.const_mul _)
  simp_rw [hpt]
  refine ⟨hint, ?_⟩
  have e1 := integral_add (μ := stdGaussian E)
    (f := fun v => ‖x - xstar‖ ^ 2 - 2 * h * (⟪v, x - xstar⟫ * coef f μ x v))
    (g := fun v => h ^ 2 * (coef f μ x v ^ 2 * ‖v‖ ^ 2))
    ((integrable_const _).sub (hi1.const_mul _)) (hi2.const_mul _)
  have e2 := integral_sub (μ := stdGaussian E) (f := fun _ => ‖x - xstar‖ ^ 2)
    (g := fun v => 2 * h * (⟪v, x - xstar⟫ * coef f μ x v)) (integrable_const _)
    (hi1.const_mul _)
  try simp only at e1 e2
  rw [e1, e2, integral_const, integral_const_mul, integral_const_mul]
  simp only [probReal_univ, one_smul]
  have J1 := I1 (xstar := xstar) hL hdiff hgrad hf hμ x
  have J2 := I2 hL hdiff hgrad hf hμ x
  have J3 := grad_sq_le hL hdiff hgrad hopt x
  rw [← hn] at J1 J2
  have hF : 0 ≤ f x - f xstar := sub_nonneg.mpr (hopt x)
  have hpos : 0 < 4 * (n + 4) * L := by positivity
  have hh0 : 0 < h := by rw [hh]; positivity
  have hL4 : h * (4 * (n + 4) * L) = 1 := by rw [hh]; field_simp
  have hhL : h * L * (n + 4) = 1 / 4 := by linarith
  have t1 : h ^ 2 * (2 * (n + 2) * ‖gradient f x‖ ^ 2) ≤ h * (f x - f xstar) := by
    have a1 : h ^ 2 * (2 * (n + 2) * ‖gradient f x‖ ^ 2) ≤
        h ^ 2 * (2 * (n + 2) * (2 * L * (f x - f xstar))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left J3 (by positivity)) (by positivity)
    have a2 : h ^ 2 * (2 * (n + 2) * (2 * L * (f x - f xstar))) ≤
        h ^ 2 * (4 * (n + 4) * L * (f x - f xstar)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith [mul_nonneg hL.le hF]
    have a3 : h ^ 2 * (4 * (n + 4) * L * (f x - f xstar)) = h * (f x - f xstar) := by
      calc h ^ 2 * (4 * (n + 4) * L * (f x - f xstar))
          = h * (h * (4 * (n + 4) * L)) * (f x - f xstar) := by ring
        _ = _ := by rw [hL4]; ring
    linarith
  have t2 : h ^ 2 * (L ^ 2 * μ ^ 2 / 2 * ((n + 4) * (n + 2) * n)) =
      h * L * μ ^ 2 * ((n + 2) * n / 8) := by
    calc h ^ 2 * (L ^ 2 * μ ^ 2 / 2 * ((n + 4) * (n + 2) * n))
        = h * L * μ ^ 2 * (h * L * (n + 4)) * ((n + 2) * n / 2) := by ring
      _ = _ := by rw [hhL]; ring
  have t3 : n + (n + 2) * n / 8 ≤ 9 * (n + 4) ^ 2 / 25 := by nlinarith
  have t4 : h * L * μ ^ 2 * (n + (n + 2) * n / 8) ≤ h * L * μ ^ 2 * (9 * (n + 4) ^ 2 / 25) :=
    mul_le_mul_of_nonneg_left t3 (by positivity)
  have J1' : 2 * h * (f x - f xstar - L * μ ^ 2 / 2 * n) ≤
      2 * h * ∫ v, ⟪v, x - xstar⟫ * coef f μ x v ∂stdGaussian E :=
    mul_le_mul_of_nonneg_left J1 (by positivity)
  have J2' : h ^ 2 * ∫ v, coef f μ x v ^ 2 * ‖v‖ ^ 2 ∂stdGaussian E ≤
      h ^ 2 * (2 * (n + 2) * ‖gradient f x‖ ^ 2 +
        L ^ 2 * μ ^ 2 / 2 * ((n + 4) * (n + 2) * n)) :=
    mul_le_mul_of_nonneg_left J2 (by positivity)
  nlinarith

end core


/-! ### The random run -/

section run

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

lemma oracle_eq {f : E → ℝ} {μ : ℝ} (hdiff : Differentiable ℝ f) (y v : E) :
    RandomGradFree.Shared.oracle f μ y v = coef f μ y v • v := by
  unfold RandomGradFree.Shared.oracle coef
  split_ifs with h0
  · congr 1
    have hd := line_deriv hdiff y v 0
    rw [zero_smul, add_zero] at hd
    have ht := hasDerivAt_iff_tendsto_slope_zero.mp hd
    have ht2 : Filter.Tendsto (fun α : ℝ => (f (y + α • v) - f y) / α)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds ⟪gradient f y, v⟫) := by
      refine (ht.mono_left (nhdsWithin_mono _ ?_)).congr ?_
      · intro t (htt : 0 < t); exact htt.ne'
      · intro t; simp only [zero_add, zero_smul, add_zero, smul_eq_mul]; rw [div_eq_inv_mul]
    exact ht2.limUnder_eq
  · rfl

lemma run_facts {f : E → ℝ} {L μ h : ℝ} (hL : 0 < L) (hdiff : Differentiable ℝ f)
    (hgrad : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hf : ConvexOn ℝ Set.univ f) {xstar : E} (hopt : ∀ y, f xstar ≤ f y) (hμ : 0 ≤ μ)
    (hh : h = 1 / (4 * ((Module.finrank ℝ E : ℝ) + 4) * L)) {x₀ : E}
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {u : ℕ → Ω → E} {x : ℕ → Ω → E} (hrun : RandomGradFree.Smooth.IsRandomGradientRun P f μ h x₀ u x) :
    ∃ R Ev : ℕ → ℝ, R 0 = ‖x₀ - xstar‖ ^ 2 ∧ (∀ k, 0 ≤ R k) ∧
      (∀ k, R (k + 1) + h * Ev k ≤
        R k + h * μ ^ 2 * L * (9 * ((Module.finrank ℝ E : ℝ) + 4) ^ 2 / 25)) ∧
      (∀ k, (∫ ω, f (x k ω) ∂P) - f xstar = Ev k) ∧
      (∀ c : ℝ, 0 ≤ c → (∀ y, c * ‖y - xstar‖ ^ 2 ≤ f y - f xstar) → ∀ k, c * R k ≤ Ev k) ∧
      (∀ k, Ev k ≤ L / 2 * R k) := by
  have hu : ∀ k, Measurable (u k) := hrun.measurable_dir
  let 𝓕 : ℕ → MeasurableSpace Ω := fun k =>
    ⨆ j ∈ Set.Iio k, (inferInstance : MeasurableSpace E).comap (u j)
  have h𝓕le : ∀ k, 𝓕 k ≤ ‹MeasurableSpace Ω› := fun k => iSup₂_le fun j _ => (hu j).comap_le
  have hSc : Continuous (fun p : E × E => p.1 - h • (coef f μ p.1 p.2 • p.2)) :=
    continuous_fst.sub (continuous_const.smul
      ((coef_cont_joint (μ := μ) hdiff hgrad).smul continuous_snd))
  have hS : Measurable (fun p : E × E => p.1 - h • (coef f μ p.1 p.2 • p.2)) := hSc.measurable
  have hstep : ∀ k, x (k + 1) =
      fun ω => (fun p : E × E => p.1 - h • (coef f μ p.1 p.2 • p.2)) (x k ω, u k ω) :=
    fun k => funext fun ω => by rw [hrun.step, oracle_eq hdiff]
  have hx𝓕 : ∀ k, Measurable[𝓕 k] (x k) := by
    intro k
    induction k with
    | zero => rw [hrun.init]; exact measurable_const
    | succ k ih =>
      rw [hstep k]
      have hmono : 𝓕 k ≤ 𝓕 (k + 1) := iSup₂_le fun j hj =>
        le_iSup₂_of_le (f := fun j (_ : j ∈ Set.Iio (k + 1)) =>
          (inferInstance : MeasurableSpace E).comap (u j)) j
          (show j ∈ Set.Iio (k + 1) from lt_trans hj (Nat.lt_succ_self k)) le_rfl
      have huk : Measurable[𝓕 (k + 1)] (u k) := Measurable.of_comap_le
        (le_iSup₂_of_le (f := fun j (_ : j ∈ Set.Iio (k + 1)) =>
          (inferInstance : MeasurableSpace E).comap (u j)) k
          (show k ∈ Set.Iio (k + 1) from Nat.lt_succ_self k) le_rfl)
      exact hS.comp ((ih.mono hmono le_rfl).prodMk huk)
  have hxm : ∀ k, Measurable (x k) := fun k => (hx𝓕 k).mono (h𝓕le k) le_rfl
  have hind : ∀ k, IndepFun (x k) (u k) P := by
    intro k
    have hI := indep_iSup_of_disjoint
      (m := fun j => (inferInstance : MeasurableSpace E).comap (u j))
      (fun j => (hu j).comap_le) hrun.indep_dir.iIndep (S := Set.Iio k) (T := {k})
      (Set.disjoint_singleton_right.mpr (lt_irrefl k))
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le_right (indep_of_indep_of_le_left hI (hx𝓕 k).comap_le)
      (le_iSup₂_of_le (f := fun j (_ : j ∈ ({k} : Set ℕ)) =>
          (inferInstance : MeasurableSpace E).comap (u j)) k (Set.mem_singleton k) le_rfl)
  have htr : ∀ k (G : E × E → ENNReal), Measurable G →
      ∫⁻ ω, G (x k ω, u k ω) ∂P = ∫⁻ ω, (∫⁻ v, G (x k ω, v) ∂stdGaussian E) ∂P := by
    intro k G hG
    have hmap : P.map (fun ω => (x k ω, u k ω)) = (P.map (x k)).prod (stdGaussian E) := by
      rw [← hrun.law_dir k]
      exact (indepFun_iff_map_prod_eq_prod_map_map (hxm k).aemeasurable
        (hu k).aemeasurable).mp (hind k)
    rw [← lintegral_map hG ((hxm k).prodMk (hu k)), hmap, lintegral_prod _ hG.aemeasurable,
      lintegral_map hG.lintegral_prod_right' (hxm k)]
  set c0 := h * μ ^ 2 * L * (9 * ((Module.finrank ℝ E : ℝ) + 4) ^ 2 / 25) with hc0def
  have hh0 : 0 < h := by rw [hh]; positivity
  have hc0 : 0 ≤ c0 := by positivity
  let r : ℕ → ENNReal := fun k => ∫⁻ ω, ENNReal.ofReal (‖x k ω - xstar‖ ^ 2) ∂P
  let e : ℕ → ENNReal := fun k => ∫⁻ ω, ENNReal.ofReal (f (x k ω) - f xstar) ∂P
  have hpt : ∀ y : E, (∫⁻ v, ENNReal.ofReal (‖y - h • (coef f μ y v • v) - xstar‖ ^ 2)
      ∂stdGaussian E) + ENNReal.ofReal h * ENNReal.ofReal (f y - f xstar) ≤
      ENNReal.ofReal (‖y - xstar‖ ^ 2) + ENNReal.ofReal c0 := by
    intro y
    obtain ⟨hi, hb⟩ := step_bound hL hdiff hgrad hf hopt hμ hh y
    rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun v => by positivity)]
    have hI0 : 0 ≤ ∫ v, ‖y - h • (coef f μ y v • v) - xstar‖ ^ 2 ∂stdGaussian E :=
      integral_nonneg fun v => by positivity
    have hF : 0 ≤ f y - f xstar := sub_nonneg.mpr (hopt y)
    rw [← ENNReal.ofReal_mul hh0.le]
    calc ENNReal.ofReal (∫ v, ‖y - h • (coef f μ y v • v) - xstar‖ ^ 2 ∂stdGaussian E) +
          ENNReal.ofReal (h * (f y - f xstar))
        ≤ ENNReal.ofReal (‖y - xstar‖ ^ 2 - h * (f y - f xstar) + c0) +
          ENNReal.ofReal (h * (f y - f xstar)) := add_le_add (ENNReal.ofReal_le_ofReal hb) le_rfl
      _ = ENNReal.ofReal (‖y - xstar‖ ^ 2 + c0) := by
          rw [← ENNReal.ofReal_add (by linarith) (by positivity)]; congr 1; ring
      _ ≤ _ := ENNReal.ofReal_add_le
  have hGm : Measurable fun p : E × E =>
      ENNReal.ofReal (‖p.1 - h • (coef f μ p.1 p.2 • p.2) - xstar‖ ^ 2) :=
    ((hSc.sub continuous_const).norm.pow 2).measurable.ennreal_ofReal
  have hmeasF : ∀ k, Measurable fun ω => ENNReal.ofReal (f (x k ω) - f xstar) := fun k =>
    ((hdiff.continuous.measurable.comp (hxm k)).sub_const _).ennreal_ofReal
  have hmeasR : ∀ k, Measurable fun ω => ENNReal.ofReal (‖x k ω - xstar‖ ^ 2) := fun k =>
    (((continuous_id.sub continuous_const).norm.pow 2).measurable.comp (hxm k)).ennreal_ofReal
  have hrec : ∀ k, r (k + 1) + ENNReal.ofReal h * e k ≤ r k + ENNReal.ofReal c0 := by
    intro k
    have e1 : r (k + 1) = ∫⁻ ω, (∫⁻ v, ENNReal.ofReal
        (‖x k ω - h • (coef f μ (x k ω) v • v) - xstar‖ ^ 2) ∂stdGaussian E) ∂P := by
      simp only [r]; rw [hstep k]; exact htr k _ hGm
    rw [e1]
    simp only [e]
    have hGi : Measurable (fun ω => ∫⁻ v, ENNReal.ofReal
        (‖x k ω - h • (coef f μ (x k ω) v • v) - xstar‖ ^ 2) ∂stdGaussian E) :=
      (hGm.lintegral_prod_right').comp (hxm k)
    rw [← lintegral_const_mul _ (hmeasF k), ← lintegral_add_left hGi]
    calc _ ≤ ∫⁻ ω, (ENNReal.ofReal (‖x k ω - xstar‖ ^ 2) + ENNReal.ofReal c0) ∂P :=
          lintegral_mono fun ω => hpt (x k ω)
      _ = r k + ENNReal.ofReal c0 := by
          rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
  have hr0 : r 0 = ENNReal.ofReal (‖x₀ - xstar‖ ^ 2) := by
    simp only [r]; rw [hrun.init]; simp
  have hrfin : ∀ k, r k ≠ ⊤ := by
    intro k
    induction k with
    | zero => rw [hr0]; exact ENNReal.ofReal_ne_top
    | succ k ih =>
      exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨ih, ENNReal.ofReal_ne_top⟩)
        (le_trans le_self_add (hrec k))
  have hefin : ∀ k, e k ≠ ⊤ := by
    intro k hk
    have := hrec k
    rw [hk, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hh0).ne', add_top] at this
    exact (ENNReal.add_ne_top.mpr ⟨hrfin k, ENNReal.ofReal_ne_top⟩) (top_le_iff.mp this)
  refine ⟨fun k => (r k).toReal, fun k => (e k).toReal, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (r 0).toReal = _
    rw [hr0, ENNReal.toReal_ofReal (by positivity)]
  · intro k; exact ENNReal.toReal_nonneg
  · intro k
    have := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hrfin k, ENNReal.ofReal_ne_top⟩) (hrec k)
    rw [ENNReal.toReal_add (hrfin (k + 1)) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hefin k)),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hh0.le,
      ENNReal.toReal_add (hrfin k) ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hc0] at this
    exact this
  · intro k
    have hnn : ∀ ω, 0 ≤ f (x k ω) - f xstar := fun ω => sub_nonneg.mpr (hopt _)
    have hmeas : AEStronglyMeasurable (fun ω => f (x k ω) - f xstar) P :=
      ((hdiff.continuous.measurable.comp (hxm k)).sub_const _).aestronglyMeasurable
    have hint : Integrable (fun ω => f (x k ω) - f xstar) P :=
      ⟨hmeas, (hasFiniteIntegral_iff_ofReal (ae_of_all _ hnn)).mpr
        (lt_top_iff_ne_top.mpr (hefin k))⟩
    have h1 : ∫ ω, (f (x k ω) - f xstar) ∂P = (e k).toReal :=
      integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hnn) hmeas
    have hfi : Integrable (fun ω => f (x k ω)) P :=
      (hint.add (integrable_const (f xstar))).congr (ae_of_all _ fun ω => by simp)
    have h2 : ∫ ω, (f (x k ω) - f xstar) ∂P = (∫ ω, f (x k ω) ∂P) - f xstar := by
      rw [integral_sub hfi (integrable_const _), integral_const, probReal_univ, one_smul]
    show _ = (e k).toReal
    rw [← h2, h1]
  · intro c hc hcb k
    have h1 : ENNReal.ofReal c * r k ≤ e k := by
      simp only [r, e]
      rw [← lintegral_const_mul _ (hmeasR k)]
      exact lintegral_mono fun ω => by
        rw [← ENNReal.ofReal_mul hc]; exact ENNReal.ofReal_le_ofReal (hcb _)
    have := ENNReal.toReal_mono (hefin k) h1
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc] at this
  · intro k
    have hg0 : gradient f xstar = 0 := grad_star hL hdiff hgrad hopt
    have h1 : e k ≤ ENNReal.ofReal (L / 2) * r k := by
      simp only [r, e]
      rw [← lintegral_const_mul _ (hmeasR k)]
      exact lintegral_mono fun ω => by
        rw [← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        have := descent hdiff hgrad xstar (x k ω)
        rw [hg0, inner_zero_left] at this
        linarith
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hrfin k)) h1
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at this

end run

end RG33

open MeasureTheory ProbabilityTheory RandomGradFree.Smooth in
theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (hdim : 2 ≤ Module.finrank ℝ E)
    (f : E → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (L₁ : ℝ) (hL₁ : 0 < L₁) (hdiff : Differentiable ℝ f)
    (hgrad : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L₁ * ‖x - y‖)
    (xstar : E) (hopt : ∀ y, f xstar ≤ f y)
    (μ : ℝ) (hμ : 0 ≤ μ) (h : ℝ) (hh : h = 1 / (4 * ((Module.finrank ℝ E : ℝ) + 4) * L₁))
    (x₀ : E) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (u : ℕ → Ω → E) (x : ℕ → Ω → E)
    (hrun : IsRandomGradientRun P f μ h x₀ u x) :
    (∀ N : ℕ,
      (1 / ((N : ℝ) + 1)) * ∑ k ∈ Finset.range (N + 1), ((∫ ω, f (x k ω) ∂P) - f xstar)
        ≤ 4 * ((Module.finrank ℝ E : ℝ) + 4) * L₁ * ‖x₀ - xstar‖ ^ 2 / ((N : ℝ) + 1)
          + 9 * μ ^ 2 * ((Module.finrank ℝ E : ℝ) + 4) ^ 2 * L₁ / 25) ∧
    (∀ τ : ℝ, 0 < τ →
      (∀ y z, f z ≥ f y + inner ℝ (gradient f y) (z - y) + τ / 2 * ‖z - y‖ ^ 2) →
      ∀ N : ℕ,
        (∫ ω, f (x N ω) ∂P) - f xstar
          ≤ 1 / 2 * L₁ *
            (18 * μ ^ 2 * ((Module.finrank ℝ E : ℝ) + 4) ^ 2 / (25 * τ) * L₁
              + (1 - τ / (8 * ((Module.finrank ℝ E : ℝ) + 4) * L₁)) ^ N
                * (‖x₀ - xstar‖ ^ 2
                  - 18 * μ ^ 2 * ((Module.finrank ℝ E : ℝ) + 4) ^ 2 / (25 * τ) * L₁))) := by
  obtain ⟨R, Ev, hR0, hRnn, hrec, hEv, hlow, hup⟩ :=
    RG33.run_facts hL₁ hdiff hgrad hf hopt hμ hh hrun
  set n : ℝ := (Module.finrank ℝ E : ℝ) with hn
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hh0 : 0 < h := by rw [hh]; positivity
  have hL4 : h * (4 * (n + 4) * L₁) = 1 := by rw [hh]; field_simp
  constructor
  · intro N
    have hsum : ∀ M : ℕ, R M + h * ∑ k ∈ Finset.range M, Ev k ≤
        R 0 + M * (h * μ ^ 2 * L₁ * (9 * (n + 4) ^ 2 / 25)) := by
      intro M
      induction M with
      | zero => simp
      | succ M ih =>
        rw [Finset.sum_range_succ, mul_add]
        have := hrec M
        push_cast
        linarith
    have h1 := hsum (N + 1)
    have h2 := hRnn (N + 1)
    rw [hR0] at h1
    simp_rw [hEv]
    have hSumB : ∑ k ∈ Finset.range (N + 1), Ev k ≤
        4 * (n + 4) * L₁ * ‖x₀ - xstar‖ ^ 2 + ((N : ℝ) + 1) * (9 * μ ^ 2 * (n + 4) ^ 2 * L₁ / 25) := by
      have a1 : h * ∑ k ∈ Finset.range (N + 1), Ev k ≤
          ‖x₀ - xstar‖ ^ 2 + ((N : ℝ) + 1) * (h * μ ^ 2 * L₁ * (9 * (n + 4) ^ 2 / 25)) := by
        push_cast at h1; linarith
      have e : ∑ k ∈ Finset.range (N + 1), Ev k =
          (h * ∑ k ∈ Finset.range (N + 1), Ev k) * (4 * (n + 4) * L₁) := by
        rw [mul_comm h, mul_assoc, hL4, mul_one]
      rw [e]
      calc (h * ∑ k ∈ Finset.range (N + 1), Ev k) * (4 * (n + 4) * L₁)
          ≤ (‖x₀ - xstar‖ ^ 2 + ((N : ℝ) + 1) * (h * μ ^ 2 * L₁ * (9 * (n + 4) ^ 2 / 25))) *
              (4 * (n + 4) * L₁) := mul_le_mul_of_nonneg_right a1 (by positivity)
        _ = 4 * (n + 4) * L₁ * ‖x₀ - xstar‖ ^ 2 + ((N : ℝ) + 1) *
              (μ ^ 2 * L₁ * (9 * (n + 4) ^ 2 / 25) * (h * (4 * (n + 4) * L₁))) := by ring
        _ = _ := by rw [hL4]; ring
    have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    calc 1 / ((N : ℝ) + 1) * ∑ k ∈ Finset.range (N + 1), Ev k
        ≤ 1 / ((N : ℝ) + 1) * (4 * (n + 4) * L₁ * ‖x₀ - xstar‖ ^ 2 +
            ((N : ℝ) + 1) * (9 * μ ^ 2 * (n + 4) ^ 2 * L₁ / 25)) :=
          mul_le_mul_of_nonneg_left hSumB (by positivity)
      _ = _ := by field_simp
  · intro τ hτ hsc N
    have hg0 : gradient f xstar = 0 := RG33.grad_star hL₁ hdiff hgrad hopt
    have hlowτ : ∀ y, τ / 2 * ‖y - xstar‖ ^ 2 ≤ f y - f xstar := by
      intro y
      have := hsc xstar y
      rw [hg0, inner_zero_left] at this
      linarith
    have hτL : τ ≤ L₁ := by
      have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (lt_of_lt_of_le (by norm_num) hdim)
      obtain ⟨v, hv⟩ := exists_ne (0 : E)
      have h1 := hlowτ (xstar + v)
      have h2 := RG33.descent hdiff hgrad xstar (xstar + v)
      rw [hg0, inner_zero_left, add_sub_cancel_left] at h2
      rw [add_sub_cancel_left] at h1
      have hv2 : 0 < ‖v‖ ^ 2 := by positivity
      nlinarith
    have hpos : 0 < 8 * (n + 4) * L₁ := by positivity
    set q := 1 - τ / (8 * (n + 4) * L₁) with hq
    set δ := 18 * μ ^ 2 * (n + 4) ^ 2 / (25 * τ) * L₁ with hδ
    have hq0 : 0 ≤ q := by
      have : τ / (8 * (n + 4) * L₁) ≤ 1 := by
        rw [div_le_one hpos]; nlinarith
      linarith
    have e1 : (1 - q) * δ = h * μ ^ 2 * L₁ * (9 * (n + 4) ^ 2 / 25) := by
      rw [hq, hδ, hh]; field_simp; ring
    have e2 : h * (τ / 2) = 1 - q := by
      rw [hq, hh]; field_simp; ring
    have hqrec : ∀ k, R (k + 1) ≤ q * R k + (1 - q) * δ := by
      intro k
      have a1 := hrec k
      have a2 := hlow (τ / 2) (by positivity) hlowτ k
      have a3 : h * (τ / 2 * R k) ≤ h * Ev k := mul_le_mul_of_nonneg_left a2 hh0.le
      have a4 : h * (τ / 2 * R k) = (1 - q) * R k := by rw [← mul_assoc, e2]
      rw [e1]
      linarith
    have hRN : ∀ k, R k ≤ δ + q ^ k * (R 0 - δ) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        calc R (k + 1) ≤ q * R k + (1 - q) * δ := hqrec k
          _ ≤ q * (δ + q ^ k * (R 0 - δ)) + (1 - q) * δ := by
              linarith [mul_le_mul_of_nonneg_left ih hq0]
          _ = δ + q ^ (k + 1) * (R 0 - δ) := by ring
    have hE := hup N
    rw [← hEv N] at hE
    rw [hR0] at hRN
    calc (∫ ω, f (x N ω) ∂P) - f xstar ≤ L₁ / 2 * R N := hE
      _ ≤ L₁ / 2 * (δ + q ^ N * (‖x₀ - xstar‖ ^ 2 - δ)) :=
          mul_le_mul_of_nonneg_left (hRN N) (by positivity)
      _ = _ := by ring
