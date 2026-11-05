-- Prove2me | solution 1 for SLPricing.Compare.proposition_8
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T08:40:25.088979+00:00
-- url     : https://prove2.me/submissions/16c8a31a-a56b-4c9e-b7b5-f72943ce8609

import Mathlib
import Definitions.Def_SLPricing_Compare_Model
import Theorems.Thm_SLPricing_Compare_lemma_3
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace SLP8
open SLPricing.Compare

/-! ## Gaussian foundations -/

noncomputable def rr (P : Params) (m : ℝ) : ℝ := max m 0 * P.γ / (max m 0 * P.γ + 1)

noncomputable def sd (P : Params) (m : ℝ) : ℝ := Real.sqrt (P.σp ^ 2 * rr P m)

lemma den_pos (P : Params) (hP : P.Standing) (m : ℝ) : 0 < max m 0 * P.γ + 1 := by
  have := mul_nonneg (le_max_right m 0) hP.γ_nonneg
  linarith

lemma rr_nonneg (P : Params) (hP : P.Standing) (m : ℝ) : 0 ≤ rr P m :=
  div_nonneg (mul_nonneg (le_max_right _ _) hP.γ_nonneg) (den_pos P hP m).le

lemma rr_le_one (P : Params) (hP : P.Standing) (m : ℝ) : rr P m ≤ 1 := by
  unfold rr
  rw [div_le_one (den_pos P hP m)]
  linarith

lemma rr_zero (P : Params) : rr P 0 = 0 := by simp [rr]

lemma rr_lip (P : Params) (hP : P.Standing) (m m' : ℝ) :
    |rr P m - rr P m'| ≤ P.γ * |m - m'| := by
  unfold rr
  set a := max m 0 * P.γ
  set b := max m' 0 * P.γ
  have ha : 0 ≤ a := mul_nonneg (le_max_right _ _) hP.γ_nonneg
  have hb : 0 ≤ b := mul_nonneg (le_max_right _ _) hP.γ_nonneg
  have hab : |a - b| ≤ P.γ * |m - m'| := by
    have : a - b = (max m 0 - max m' 0) * P.γ := by ring
    rw [this, abs_mul, abs_of_nonneg hP.γ_nonneg, mul_comm]
    exact mul_le_mul_of_nonneg_left (abs_max_sub_max_le_abs _ _ _) hP.γ_nonneg
  have e : a / (a + 1) - b / (b + 1) = (a - b) / ((a + 1) * (b + 1)) := by
    field_simp; ring
  rw [e, abs_div, abs_of_pos (by positivity : (0:ℝ) < (a + 1) * (b + 1))]
  calc |a - b| / ((a + 1) * (b + 1)) ≤ |a - b| / 1 := by
        apply div_le_div_of_nonneg_left (abs_nonneg _) one_pos
        nlinarith
    _ ≤ _ := by rw [div_one]; exact hab

lemma sd_nonneg (P : Params) (m : ℝ) : 0 ≤ sd P m := Real.sqrt_nonneg _

lemma sd_sq (P : Params) (hP : P.Standing) (m : ℝ) : sd P m ^ 2 = P.σp ^ 2 * rr P m :=
  Real.sq_sqrt (mul_nonneg (sq_nonneg _) (rr_nonneg P hP m))

lemma sd_le (P : Params) (hP : P.Standing) (m : ℝ) : sd P m ≤ P.σp := by
  unfold sd
  rw [Real.sqrt_le_left hP.σp_pos.le]
  have := rr_le_one P hP m
  nlinarith [sq_nonneg P.σp]

lemma sd_zero (P : Params) : sd P 0 = 0 := by simp [sd, rr_zero]

lemma sqrt_sub_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |Real.sqrt a - Real.sqrt b| ≤ Real.sqrt |a - b| := by
  wlog h : b ≤ a generalizing a b
  · rw [abs_sub_comm, abs_sub_comm a b]; exact this b a hb ha (by linarith)
  have h1 : Real.sqrt b ≤ Real.sqrt a := Real.sqrt_le_sqrt h
  rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
  have h2 : Real.sqrt a ≤ Real.sqrt b + Real.sqrt (a - b) := by
    rw [Real.sqrt_le_left (by positivity)]
    have e1 := Real.sq_sqrt hb
    have e2 := Real.sq_sqrt (by linarith : (0:ℝ) ≤ a - b)
    nlinarith [Real.sqrt_nonneg b, Real.sqrt_nonneg (a - b)]
  linarith

lemma sd_lip (P : Params) (hP : P.Standing) (m m' : ℝ) :
    |sd P m - sd P m'| ≤ Real.sqrt (P.σp ^ 2 * P.γ * |m - m'|) := by
  unfold sd
  refine le_trans (sqrt_sub_le _ _ (mul_nonneg (sq_nonneg _) (rr_nonneg P hP m))
    (mul_nonneg (sq_nonneg _) (rr_nonneg P hP m'))) (Real.sqrt_le_sqrt ?_)
  rw [← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg _), mul_assoc]
  exact mul_le_mul_of_nonneg_left (rr_lip P hP m m') (sq_nonneg _)

lemma continuous_rr (P : Params) (hP : P.Standing) : Continuous (rr P) := by
  unfold rr
  exact Continuous.div (by fun_prop) (by fun_prop) (fun m => (den_pos P hP m).ne')

lemma continuous_sd (P : Params) (hP : P.Standing) : Continuous (sd P) := by
  unfold sd
  exact (continuous_const.mul (continuous_rr P hP)).sqrt

lemma preVar_coe (P : Params) (hP : P.Standing) (m : ℝ) (hm : 0 ≤ m) :
    (preVar P m : ℝ) = P.σp ^ 2 * rr P m := by
  unfold preVar rr
  rw [max_eq_left hm, Real.coe_toNNReal _ (mul_nonneg (sq_nonneg _) ?_)]
  have := den_pos P hP m
  rw [max_eq_left hm] at this
  exact div_nonneg (mul_nonneg hm hP.γ_nonneg) this.le

lemma prePost_eq (P : Params) (hP : P.Standing) (m : ℝ) (hm : 0 ≤ m) :
    prePost P m = (gaussianReal 0 1).map (fun z => sd P m * z) := by
  rw [gaussianReal_map_const_mul, mul_zero, mul_one]
  unfold prePost
  congr 1
  apply NNReal.eq
  rw [preVar_coe P hP m hm, NNReal.coe_mk, sd_sq P hP]

lemma int_rep (P : Params) (hP : P.Standing) (m : ℝ) (hm : 0 ≤ m) (g : ℝ → ℝ)
    (hg : Measurable g) :
    ∫ q, g q ∂prePost P m = ∫ z, g (sd P m * z) ∂gaussianReal 0 1 := by
  rw [prePost_eq P hP m hm, integral_map (measurable_const_mul _).aemeasurable
    hg.aestronglyMeasurable]

lemma integral_sq_gauss (v : ℝ≥0) : ∫ q, q ^ 2 ∂gaussianReal 0 v = v := by
  have h := variance_eq_integral (μ := gaussianReal 0 v) (X := id) measurable_id.aemeasurable
  rw [variance_id_gaussianReal] at h
  have h0 : (gaussianReal 0 v)[id] = 0 := by
    simp only [id]; exact integral_id_gaussianReal
  rw [h0] at h
  simp only [id, sub_zero] at h
  exact h.symm

lemma integrable_sq_gauss (v : ℝ≥0) : Integrable (fun q : ℝ => q ^ 2) (gaussianReal 0 v) :=
  (memLp_id_gaussianReal 2).integrable_sq

lemma integrable_id_gauss (v : ℝ≥0) : Integrable (fun q : ℝ => q) (gaussianReal 0 v) :=
  (memLp_id_gaussianReal 1).integrable le_rfl

lemma integrable_abs_gauss (v : ℝ≥0) : Integrable (fun q : ℝ => |q|) (gaussianReal 0 v) :=
  (integrable_id_gauss v).abs

lemma integral_abs_le (v : ℝ≥0) : ∫ q, |q| ∂gaussianReal 0 v ≤ (1 + v) / 2 := by
  have h : ∫ q, |q| ∂gaussianReal 0 v ≤ ∫ q, (1 + q ^ 2) / 2 ∂gaussianReal 0 v := by
    apply integral_mono (integrable_abs_gauss v)
    · exact ((integrable_const 1).add (integrable_sq_gauss v)).div_const 2
    · intro q
      simp only
      nlinarith [sq_nonneg (|q| - 1), sq_abs q]
  rw [integral_div, integral_add (integrable_const _) (integrable_sq_gauss v),
    integral_sq_gauss] at h
  simpa using h

lemma integral_abs_N01 : ∫ z, |z| ∂gaussianReal 0 1 ≤ 1 := by
  have := integral_abs_le 1
  simp at this
  linarith

/-- integrability of a function with linear growth -/
lemma integrable_of_lin (v : ℝ≥0) (g : ℝ → ℝ) (hg : Measurable g) (A B : ℝ)
    (hb : ∀ q, |g q| ≤ A + B * |q|) : Integrable g (gaussianReal 0 v) := by
  refine Integrable.mono' ((integrable_const A).add ((integrable_abs_gauss v).const_mul B))
    hg.aestronglyMeasurable (ae_of_all _ ?_)
  intro q
  simpa [Real.norm_eq_abs] using hb q

lemma lip_cmp (g : ℝ → ℝ) (hg : Continuous g) (hL : ∀ a b, |g a - g b| ≤ |a - b|) (s s' : ℝ) :
    |∫ z, g (s * z) ∂gaussianReal 0 1 - ∫ z, g (s' * z) ∂gaussianReal 0 1| ≤ |s - s'| := by
  have hint : ∀ t : ℝ, Integrable (fun z => g (t * z)) (gaussianReal 0 1) := by
    intro t
    refine integrable_of_lin 1 _ (hg.measurable.comp (measurable_const_mul t)) (|g 0|) |t| ?_
    intro z
    have := hL (t * z) 0
    rw [sub_zero, abs_mul] at this
    have := abs_sub_abs_le_abs_sub (g (t * z)) (g 0)
    linarith
  rw [← integral_sub (hint s) (hint s')]
  calc |∫ z, (g (s * z) - g (s' * z)) ∂gaussianReal 0 1|
      ≤ ∫ z, |g (s * z) - g (s' * z)| ∂gaussianReal 0 1 := abs_integral_le_integral_abs
    _ ≤ ∫ z, |s - s'| * |z| ∂gaussianReal 0 1 := by
        apply integral_mono ((hint s).sub (hint s')).abs
        · exact (integrable_abs_gauss 1).const_mul _
        · intro z
          have := hL (s * z) (s' * z)
          rw [← sub_mul, abs_mul] at this
          exact this
    _ = |s - s'| * ∫ z, |z| ∂gaussianReal 0 1 := integral_const_mul _ _
    _ ≤ |s - s'| * 1 := mul_le_mul_of_nonneg_left integral_abs_N01 (abs_nonneg _)
    _ = |s - s'| := mul_one _

instance prePost_prob (P : Params) (m : ℝ) : IsProbabilityMeasure (prePost P m) := by
  unfold prePost; infer_instance

/-! ## Closed forms -/

noncomputable def L (θ p q : ℝ) : ℝ := max (θ - max 0 (p - q)) 0

noncomputable def s2 (c q θ : ℝ) : ℝ := max c (max ((q + c + θ) / 2) q)

noncomputable def V (c θ q : ℝ) : ℝ := (s2 c q θ - c) * L θ (s2 c q θ) q

noncomputable def D (c x θ q : ℝ) : ℝ := max (x + q - s2 c q θ) 0

lemma late_eq (θ : ℝ) (hx : θ ∈ Icc (0 : ℝ) 1) (p q : ℝ) :
    lateMass (Icc θ 1) p q = L θ p q := by
  unfold lateMass L
  have hset : {x ∈ Icc (0 : ℝ) 1 \ Icc θ 1 | p ≤ x + q} = Ico (max 0 (p - q)) θ := by
    ext x
    simp only [mem_setOf_eq, mem_diff, mem_Icc, mem_Ico, max_le_iff, not_and, not_le]
    constructor
    · rintro ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩
      refine ⟨⟨h0, by linarith⟩, ?_⟩
      by_contra h
      push_neg at h
      exact absurd (h2 h) (not_lt.mpr h1)
    · rintro ⟨⟨h0, h3⟩, h4⟩
      exact ⟨⟨⟨h0, by linarith [hx.2]⟩, fun h => absurd h (not_le.mpr h4)⟩, by linarith⟩
  rw [hset, Real.volume_Ico, ENNReal.toReal_ofReal']

lemma L_nonneg (θ p q : ℝ) : 0 ≤ L θ p q := le_max_right _ _

lemma L_le (θ p q : ℝ) (h : 0 ≤ θ) : L θ p q ≤ θ := by
  unfold L
  apply max_le _ h
  linarith [le_max_left 0 (p - q)]

lemma L_lip (θ p a b : ℝ) : |L θ p a - L θ p b| ≤ |a - b| := by
  unfold L
  refine le_trans (abs_max_sub_max_le_abs _ _ _) ?_
  have : θ - max 0 (p - a) - (θ - max 0 (p - b)) = -(max (p - a) 0 - max (p - b) 0) := by
    rw [max_comm 0, max_comm 0]; ring
  rw [this, abs_neg]
  refine le_trans (abs_max_sub_max_le_abs _ _ _) ?_
  rw [show p - a - (p - b) = -(a - b) by ring, abs_neg]

lemma L_zero (p q : ℝ) : L 0 p q = 0 := by
  unfold L
  apply le_antisymm _ (le_max_right _ _)
  apply max_le _ le_rfl
  linarith [le_max_left 0 (p - q)]

lemma continuous_L : Continuous (fun x : ℝ × ℝ × ℝ => L x.1 x.2.1 x.2.2) := by
  unfold L; fun_prop

lemma p2Star_eq (c q θ : ℝ) (hθ : 0 ≤ θ) : SLPricing.Resp.p2Star c q θ = s2 c q θ := by
  unfold SLPricing.Resp.p2Star s2
  split_ifs with h1 h2
  · rw [max_eq_left]; apply max_le <;> linarith
  · rw [max_eq_right (by apply le_max_of_le_left; linarith), max_eq_left (by linarith)]
  · rw [max_eq_right (by apply le_max_of_le_right; linarith), max_eq_right (by linarith)]

lemma s2_ge_q (c q θ : ℝ) : q ≤ s2 c q θ := le_trans (le_max_right _ _) (le_max_right _ _)
lemma s2_ge_c (c q θ : ℝ) : c ≤ s2 c q θ := le_max_left _ _

lemma continuous_s2 (c : ℝ) : Continuous (fun x : ℝ × ℝ => s2 c x.1 x.2) := by
  unfold s2; fun_prop

lemma L_s2 (c q θ : ℝ) : L θ (s2 c q θ) q = max (θ + q - s2 c q θ) 0 := by
  unfold L
  rw [max_eq_right (by linarith [s2_ge_q c q θ] : (0:ℝ) ≤ s2 c q θ - q)]
  ring_nf

lemma V_nonneg (c θ q : ℝ) : 0 ≤ V c θ q :=
  mul_nonneg (by linarith [s2_ge_c c q θ]) (L_nonneg _ _ _)

lemma s2_sub_le (c q θ : ℝ) (hc : 0 ≤ c) (hθ : θ ≤ 1) : s2 c q θ - c ≤ 1 + |q| := by
  unfold s2
  have := le_abs_self q
  have := neg_abs_le q
  have h3 : max c (max ((q + c + θ) / 2) q) ≤ c + 1 + |q| := by
    apply max_le (by linarith [abs_nonneg q]) (max_le (by linarith) (by linarith))
  linarith

lemma V_le (c θ q : ℝ) (hc : 0 ≤ c) (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1) : V c θ q ≤ 1 + |q| := by
  unfold V
  have h1 := s2_sub_le c q θ hc hθ
  have h2 := L_le θ (s2 c q θ) q hθ0
  have h3 := L_nonneg θ (s2 c q θ) q
  have h4 : 0 ≤ s2 c q θ - c := by linarith [s2_ge_c c q θ]
  nlinarith [abs_nonneg q]

lemma continuous_V (c : ℝ) : Continuous (fun x : ℝ × ℝ => V c x.1 x.2) := by
  have h1 : Continuous (fun x : ℝ × ℝ => s2 c x.2 x.1) :=
    (continuous_s2 c).comp (continuous_snd.prodMk continuous_fst)
  unfold V
  refine (h1.sub continuous_const).mul ?_
  exact continuous_L.comp (continuous_fst.prodMk (h1.prodMk continuous_snd))

lemma D_nonneg (c x θ q : ℝ) : 0 ≤ D c x θ q := le_max_right _ _

lemma D_le (c x θ q : ℝ) (hx : 0 ≤ x) : D c x θ q ≤ x := by
  unfold D
  exact max_le (by linarith [s2_ge_q c q θ]) hx

lemma D_mono (c x y θ q : ℝ) (h : x ≤ y) : D c y θ q ≤ D c x θ q + (y - x) := by
  unfold D
  apply max_le
  · linarith [le_max_left (x + q - s2 c q θ) 0]
  · linarith [le_max_right (x + q - s2 c q θ) 0]

lemma D_mono' (c x y θ q : ℝ) (h : x ≤ y) : D c x θ q ≤ D c y θ q := by
  unfold D
  apply max_le_max _ le_rfl
  linarith

lemma continuous_D (c : ℝ) : Continuous (fun x : ℝ × ℝ × ℝ => D c x.1 x.2.1 x.2.2) := by
  unfold D
  have h1 : Continuous (fun x : ℝ × ℝ × ℝ => s2 c x.2.2 x.2.1) :=
    (continuous_s2 c).comp (continuous_snd.snd.prodMk continuous_snd.fst)
  exact ((continuous_fst.add continuous_snd.snd).sub h1).max continuous_const

lemma secondProfit_eq (P : Params) (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) (q p : ℝ) :
    secondProfit P (Icc θ 1) q p = (p - P.c) * L θ p q := by
  unfold secondProfit; rw [late_eq θ hθ]

lemma secondProfit_star (P : Params) (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) (q : ℝ) :
    secondProfit P (Icc θ 1) q (SLPricing.Resp.p2Star P.c q θ) = V P.c θ q := by
  rw [secondProfit_eq P θ hθ, p2Star_eq _ _ _ hθ.1]; rfl

/-! ## The two profit functions at δc = 0 -/

noncomputable def Fh (P : Params) (θ p₂ : ℝ) : ℝ :=
  (θ - P.c) * (1 - θ) + (p₂ - P.c) * ∫ z, L θ p₂ (sd P (1 - θ) * z) ∂gaussianReal 0 1

noncomputable def Rh (P : Params) (p ζ : ℝ) : ℝ :=
  (p - P.c) * (1 - ζ) + ∫ z, V P.c ζ (sd P (1 - ζ) * z) ∂gaussianReal 0 1

lemma Fh_cont (P : Params) (hP : P.Standing) :
    ContinuousOn (fun x : ℝ × ℝ => Fh P x.1 x.2) (Icc 0 1 ×ˢ univ) := by
  unfold Fh
  have hsd : Continuous (fun x : ℝ × ℝ => sd P (1 - x.1)) :=
    (continuous_sd P hP).comp (continuous_const.sub continuous_fst)
  refine (Continuous.continuousOn (by fun_prop)).add
    ((Continuous.continuousOn (by fun_prop)).mul ?_)
  refine continuousOn_of_dominated (bound := fun _ => 1) ?_ ?_ (integrable_const _) ?_
  · intro x _
    exact (continuous_L.comp (continuous_const.prodMk (continuous_const.prodMk
      (continuous_const.mul continuous_id)))).aestronglyMeasurable
  · intro x hx
    refine ae_of_all _ (fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (L_nonneg _ _ _)]
    exact le_trans (L_le _ _ _ hx.1.1) hx.1.2
  · refine ae_of_all _ (fun z => Continuous.continuousOn ?_)
    exact continuous_L.comp (continuous_fst.prodMk (continuous_snd.prodMk
      (hsd.mul continuous_const)))

lemma Rh_cont (P : Params) (hP : P.Standing) (p : ℝ) :
    ContinuousOn (fun ζ => Rh P p ζ) (Icc 0 1) := by
  unfold Rh
  have hsd : Continuous (fun x : ℝ => sd P (1 - x)) :=
    (continuous_sd P hP).comp (continuous_const.sub continuous_id)
  refine (Continuous.continuousOn (by fun_prop)).add ?_
  refine continuousOn_of_dominated (bound := fun z => 1 + P.σp * |z|) ?_ ?_
    ((integrable_const _).add ((integrable_abs_gauss 1).const_mul _)) ?_
  · intro x _
    exact ((continuous_V P.c).comp (continuous_const.prodMk
      (continuous_const.mul continuous_id))).aestronglyMeasurable
  · intro x hx
    refine ae_of_all _ (fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (V_nonneg _ _ _)]
    refine le_trans (V_le _ _ _ hP.c_nonneg hx.1 hx.2) ?_
    rw [abs_mul, abs_of_nonneg (sd_nonneg _ _)]
    have := sd_le P hP (1 - x)
    have := abs_nonneg z
    nlinarith
  · refine ae_of_all _ (fun z => Continuous.continuousOn ?_)
    exact (continuous_V P.c).comp (continuous_id.prodMk (hsd.mul continuous_const))

lemma measurable_L (θ p : ℝ) : Measurable (fun q => L θ p q) :=
  (continuous_L.comp (continuous_const.prodMk (continuous_const.prodMk continuous_id))).measurable

lemma measurable_V (c θ : ℝ) : Measurable (fun q => V c θ q) :=
  ((continuous_V c).comp (continuous_const.prodMk continuous_id)).measurable

lemma Fh_eq (P : Params) (hP : P.Standing) (θ p₂ : ℝ) (hθ : θ ≤ 1) :
    Fh P θ p₂ = (θ - P.c) * (1 - θ) + ∫ q, (p₂ - P.c) * L θ p₂ q ∂prePost P (1 - θ) := by
  unfold Fh
  rw [integral_const_mul, int_rep P hP (1 - θ) (by linarith) _ (measurable_L θ p₂)]

lemma Rh_eq (P : Params) (hP : P.Standing) (p ζ : ℝ) (hζ : ζ ≤ 1) :
    Rh P p ζ = (p - P.c) * (1 - ζ) + ∫ q, V P.c ζ q ∂prePost P (1 - ζ) := by
  unfold Rh
  rw [int_rep P hP (1 - ζ) (by linarith) _ (measurable_V P.c ζ)]

lemma integrable_L (v : ℝ≥0) (θ p : ℝ) (hθ : 0 ≤ θ) :
    Integrable (fun q => L θ p q) (gaussianReal 0 v) :=
  integrable_of_lin v _ (measurable_L θ p) θ 0 (fun q => by
    rw [abs_of_nonneg (L_nonneg _ _ _)]; simpa using L_le θ p q hθ)

lemma integrable_V (v : ℝ≥0) (c θ : ℝ) (hc : 0 ≤ c) (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1) :
    Integrable (fun q => V c θ q) (gaussianReal 0 v) :=
  integrable_of_lin v _ (measurable_V c θ) 1 1 (fun q => by
    rw [abs_of_nonneg (V_nonneg _ _ _)]; simpa using V_le c θ q hc hθ0 hθ)

lemma strict_gap (P : Params) (hP : P.Standing) (hγ : 0 < P.γ) (p : ℝ) (hp0 : 0 < p)
    (hp1 : p < 1) (p₂ : ℝ) : Fh P p p₂ < Rh P p p := by
  rw [Fh_eq P hP p p₂ hp1.le, Rh_eq P hP p p hp1.le]
  have hpI : p ∈ Icc (0 : ℝ) 1 := ⟨hp0.le, hp1.le⟩
  set μ := prePost P (1 - p) with hμ
  have hμ' : μ = gaussianReal 0 (preVar P (1 - p)) := rfl
  have hiL : Integrable (fun q => (p₂ - P.c) * L p p₂ q) μ := by
    rw [hμ']; exact (integrable_L _ p p₂ hp0.le).const_mul _
  have hiV : Integrable (fun q => V P.c p q) μ := by
    rw [hμ']; exact integrable_V _ P.c p hP.c_nonneg hp0.le hp1.le
  suffices h : 0 < ∫ q, (V P.c p q - (p₂ - P.c) * L p p₂ q) ∂μ by
    rw [integral_sub hiV hiL] at h
    linarith
  have hle : ∀ q, (p₂ - P.c) * L p p₂ q ≤ V P.c p q := by
    intro q
    have := (SLPricing.Compare.lemma_3 P hP (Icc p 1) p hpI rfl q).1 p₂
    rwa [secondProfit_eq P p hpI, secondProfit_star P p hpI] at this
  have hf0 : 0 ≤ fun q => V P.c p q - (p₂ - P.c) * L p p₂ q := by
    intro q; simp only [Pi.zero_apply]; linarith [hle q]
  rw [integral_pos_iff_support_of_nonneg hf0 (hiV.sub hiL)]
  -- a set of positive measure inside the support
  set S := Ioo (P.c - p) (P.c + p) \ {2 * p₂ - P.c - p} with hS
  have hSsub : S ⊆ Function.support (fun q => V P.c p q - (p₂ - P.c) * L p p₂ q) := by
    intro q ⟨hq, hq2⟩
    simp only [Function.mem_support, ne_eq]
    intro h0
    have hopt : ∀ p', secondProfit P (Icc p 1) q p' ≤ secondProfit P (Icc p 1) q p₂ := by
      intro p'
      have := (SLPricing.Compare.lemma_3 P hP (Icc p 1) p hpI rfl q).1 p'
      rw [secondProfit_star P p hpI] at this
      rw [secondProfit_eq P p hpI q p₂]
      linarith
    have := (SLPricing.Compare.lemma_3 P hP (Icc p 1) p hpI rfl q).2.1 hp0 hq.1 p₂ hopt
    unfold SLPricing.Resp.p2Star at this
    rw [if_neg (by linarith [hq.1]), if_pos hq.2.le] at this
    apply hq2
    simp only [mem_singleton_iff]
    linarith
  have hvol : volume S ≠ 0 := by
    rw [hS, measure_diff_null (measure_singleton _), Real.volume_Ioo]
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    linarith
  have hv : preVar P (1 - p) ≠ 0 := by
    intro h
    have h1 := preVar_coe P hP (1 - p) (by linarith)
    rw [h, NNReal.coe_zero] at h1
    have : 0 < rr P (1 - p) := by
      unfold rr
      rw [max_eq_left (by linarith)]
      exact div_pos (mul_pos (by linarith) hγ) (by nlinarith)
    have := mul_pos (pow_pos hP.σp_pos 2) this
    linarith
  have hac : volume ≪ μ := by rw [hμ']; exact gaussianReal_absolutelyContinuous' 0 hv
  have hμS : μ S ≠ 0 := fun h => hvol (hac h)
  exact lt_of_lt_of_le (pos_iff_ne_zero.mpr hμS) (measure_mono hSsub)

lemma R_p0 (P : Params) (hP : P.Standing) :
    (1 - P.c) ^ 2 / 3 ≤ Rh P ((2 + P.c) / 3) ((2 + P.c) / 3) := by
  set p₀ := (2 + P.c) / 3 with hp₀
  have hc0 := hP.c_nonneg
  have hc1 := hP.c_lt_one
  have hp1 : p₀ ≤ 1 := by rw [hp₀]; linarith
  have hpI : p₀ ∈ Icc (0 : ℝ) 1 := ⟨by rw [hp₀]; linarith, hp1⟩
  rw [Rh_eq P hP p₀ p₀ hp1]
  set a := (p₀ - P.c) / 2 with ha
  have hlow : ∀ q, (q + a) * a ≤ V P.c p₀ q := by
    intro q
    have := (SLPricing.Compare.lemma_3 P hP (Icc p₀ 1) p₀ hpI rfl q).1 (q + (P.c + p₀) / 2)
    rw [secondProfit_eq P p₀ hpI, secondProfit_star P p₀ hpI] at this
    refine le_trans (le_of_eq ?_) this
    unfold L
    rw [show q + (P.c + p₀) / 2 - q = (P.c + p₀) / 2 by ring,
      max_eq_right (by rw [hp₀]; linarith : (0:ℝ) ≤ (P.c + p₀) / 2),
      max_eq_left (by rw [hp₀]; linarith : (0:ℝ) ≤ p₀ - (P.c + p₀) / 2), ha]
    ring
  have hμ' : prePost P (1 - p₀) = gaussianReal 0 (preVar P (1 - p₀)) := rfl
  have hint : ∫ q, (q + a) * a ∂prePost P (1 - p₀) = a * a := by
    rw [hμ']
    simp_rw [add_mul]
    rw [integral_add ((integrable_id_gauss _).mul_const _) (integrable_const _),
      integral_mul_const, integral_id_gaussianReal]
    simp
  have hmono : ∫ q, (q + a) * a ∂prePost P (1 - p₀) ≤ ∫ q, V P.c p₀ q ∂prePost P (1 - p₀) := by
    apply integral_mono _ _ hlow
    · rw [hμ']; exact ((integrable_id_gauss _).add (integrable_const _)).mul_const _
    · rw [hμ']; exact integrable_V _ P.c p₀ hc0 hpI.1 hp1
  rw [hint] at hmono
  have : (1 - P.c) ^ 2 / 3 = (p₀ - P.c) * (1 - p₀) + a * a := by rw [ha, hp₀]; ring
  linarith

/-! ## Upper bound on pre-announced equilibrium profits for small δc -/

noncomputable def Kc (P : Params) : ℝ := 2 + P.σp ^ 2

noncomputable def errf (P : Params) (M d : ℝ) : ℝ :=
  d * Kc P + (M - P.c) * (d * Kc P + Real.sqrt (P.σp ^ 2 * P.γ * (d * Kc P)))

lemma lateMass_le_one (B : Set ℝ) (p q : ℝ) : lateMass B p q ≤ 1 := by
  unfold lateMass
  apply ENNReal.toReal_le_of_le_ofReal zero_le_one
  calc volume {x ∈ Icc (0 : ℝ) 1 \ B | p ≤ x + q} ≤ volume (Icc (0 : ℝ) 1) :=
        measure_mono (fun x hx => hx.1.1)
    _ = ENNReal.ofReal 1 := by rw [Real.volume_Icc]; norm_num

lemma lateMass_nonneg (B : Set ℝ) (p q : ℝ) : 0 ≤ lateMass B p q := ENNReal.toReal_nonneg

lemma lateMass_mono (B : Set ℝ) (p : ℝ) : Monotone (fun q => lateMass B p q) := by
  intro q q' hq
  unfold lateMass
  apply ENNReal.toReal_mono
  · exact ne_top_of_le_ne_top (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
      (measure_mono (fun x hx => hx.1.1) : volume {x ∈ Icc (0 : ℝ) 1 \ B | p ≤ x + q'} ≤
        volume (Icc (0 : ℝ) 1))
  · apply measure_mono
    intro x ⟨hx, hx'⟩
    exact ⟨hx, by linarith⟩

lemma pre_bound (P : Params) (hP : P.Standing) (d : ℝ) (hd0 : 0 ≤ d) (M : ℝ) (hM2 : 2 ≤ M)
    (Fm : ℝ) (hF : ∀ θ ∈ Icc (0 : ℝ) 1, ∀ p ∈ Icc P.c M, Fh P θ p ≤ Fm)
    (p₁ p₂ : ℝ) (B : Set ℝ) (hB : IsPreEq (P.withδc d) p₁ p₂ B) :
    preProfit P p₁ p₂ B ≤ max ((1 - P.c) ^ 2 / 4)
      (max (Fm + errf P M d) ((1 - P.c) ^ 2 / 4 + 4 * P.σp ^ 2 / M)) := by
  obtain ⟨hBm, hBsub, hbuy, hdel⟩ := hB
  have hc0 := hP.c_nonneg
  have hc1 := hP.c_lt_one
  set Q := (1 - P.c) ^ 2 / 4 with hQ
  set θ₀ := min (max p₁ 0) 1 with hθ₀def
  have hθ₀0 : 0 ≤ θ₀ := le_min (le_max_right _ _) zero_le_one
  have hθ₀1 : θ₀ ≤ 1 := min_le_right _ _
  have hθ₀I : θ₀ ∈ Icc (0 : ℝ) 1 := ⟨hθ₀0, hθ₀1⟩
  have hBθ : B ⊆ Icc θ₀ 1 := by
    intro x hx
    have h1 := (hbuy x hx).1
    have h2 := hBsub hx
    exact ⟨le_trans (min_le_left _ _) (max_le (by linarith) h2.1), h2.2⟩
  set mB := mass B with hmBdef
  have hvolB : volume B ≤ ENNReal.ofReal (1 - θ₀) := by
    rw [← Real.volume_Icc]; exact measure_mono hBθ
  have hmB0 : 0 ≤ mB := ENNReal.toReal_nonneg
  have hmB1 : mB ≤ 1 - θ₀ := ENNReal.toReal_le_of_le_ofReal (by linarith) hvolB
  have hfirst : (p₁ - P.c) * mB ≤ (θ₀ - P.c) * mB := by
    by_cases hp : p₁ ≤ 1
    · apply mul_le_mul_of_nonneg_right _ hmB0
      have : p₁ ≤ θ₀ := le_min (le_max_left _ _) hp
      linarith
    · have : B = ∅ := by
        apply eq_empty_of_forall_notMem
        intro x hx
        have h1 := (hbuy x hx).1
        have h2 := (hBsub hx).2
        push_neg at hp
        linarith
      have : mB = 0 := by rw [hmBdef, this]; simp [mass]
      rw [this]; simp
  have hfirstQ : (θ₀ - P.c) * mB ≤ Q := by
    rw [hQ]
    by_cases h : P.c ≤ θ₀
    · have : (θ₀ - P.c) * mB ≤ (θ₀ - P.c) * (1 - θ₀) := mul_le_mul_of_nonneg_left hmB1 (by linarith)
      nlinarith [sq_nonneg (θ₀ - P.c - (1 - θ₀))]
    · push_neg at h
      have : (θ₀ - P.c) * mB ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hmB0
      nlinarith [sq_nonneg (1 - P.c)]
  have hμB : prePost P mB = gaussianReal 0 (preVar P mB) := rfl
  have hlm_meas : Measurable (fun q => lateMass B p₂ q) := (lateMass_mono B p₂).measurable
  have hlm_int : Integrable (fun q => lateMass B p₂ q) (prePost P mB) := by
    rw [hμB]
    refine integrable_of_lin _ _ hlm_meas 1 0 (fun q => ?_)
    rw [abs_of_nonneg (lateMass_nonneg _ _ _)]; simpa using lateMass_le_one B p₂ q
  have hint0 : 0 ≤ ∫ q, lateMass B p₂ q ∂prePost P mB :=
    integral_nonneg (fun q => lateMass_nonneg _ _ _)
  have hpre : preProfit P p₁ p₂ B = (p₁ - P.c) * mB + (p₂ - P.c) * ∫ q, lateMass B p₂ q ∂prePost P mB := rfl
  have hvar : (preVar P mB : ℝ) ≤ P.σp ^ 2 := by
    rw [preVar_coe P hP mB hmB0]
    have := rr_le_one P hP mB
    nlinarith [sq_nonneg P.σp, rr_nonneg P hP mB]
  rw [hpre]
  rcases le_or_gt p₂ P.c with h1 | h1
  · -- case p₂ ≤ c
    have : (p₂ - P.c) * ∫ q, lateMass B p₂ q ∂prePost P mB ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hint0
    exact le_trans (by linarith) (le_max_left _ _)
  rcases le_or_gt p₂ M with h2 | h2
  swap
  · -- case p₂ > M
    have hp1 : 0 < p₂ - 1 := by linarith
    have hpt : ∀ q, lateMass B p₂ q ≤ q ^ 2 / (p₂ - 1) ^ 2 := by
      intro q
      by_cases hq : p₂ - 1 ≤ q
      · refine le_trans (lateMass_le_one B p₂ q) ?_
        rw [one_le_div (by positivity)]
        exact pow_le_pow_left₀ hp1.le hq 2
      · push_neg at hq
        have : lateMass B p₂ q = 0 := by
          unfold lateMass
          have : {x ∈ Icc (0 : ℝ) 1 \ B | p₂ ≤ x + q} = ∅ := by
            apply eq_empty_of_forall_notMem
            intro x ⟨hx, hx'⟩
            have := hx.1.2
            linarith
          rw [this]; simp
        rw [this]; positivity
    have hI : ∫ q, lateMass B p₂ q ∂prePost P mB ≤ P.σp ^ 2 / (p₂ - 1) ^ 2 := by
      calc ∫ q, lateMass B p₂ q ∂prePost P mB ≤ ∫ q, q ^ 2 / (p₂ - 1) ^ 2 ∂prePost P mB := by
            apply integral_mono hlm_int _ hpt
            rw [hμB]; exact (integrable_sq_gauss _).div_const _
        _ = (preVar P mB : ℝ) / (p₂ - 1) ^ 2 := by
            rw [integral_div, hμB, integral_sq_gauss]
        _ ≤ _ := div_le_div_of_nonneg_right hvar (by positivity)
    have hS : (p₂ - P.c) * ∫ q, lateMass B p₂ q ∂prePost P mB ≤ 4 * P.σp ^ 2 / M := by
      refine le_trans (mul_le_mul_of_nonneg_left hI (by linarith)) ?_
      rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by linarith)]
      have hs := sq_nonneg P.σp
      have : (p₂ - P.c) * M ≤ 4 * (p₂ - 1) ^ 2 := by nlinarith
      nlinarith
    refine le_trans ?_ (le_trans (le_max_right _ _) (le_max_right _ _))
    linarith
  · -- case c < p₂ ≤ M
    set K := Kc P with hK
    have hK0 : 0 ≤ K := by rw [hK, Kc]; positivity
    have hdK : 0 ≤ d * K := mul_nonneg hd0 hK0
    have hKb : ∀ x, x ≤ 1 → ∫ q, max (x + q - p₂) 0 ∂prePost P mB ≤ K := by
      intro x hx
      have hmeas : Measurable (fun q : ℝ => max (x + q - p₂) 0) := by fun_prop
      calc ∫ q, max (x + q - p₂) 0 ∂prePost P mB ≤ ∫ q, (3 + q ^ 2) / 2 ∂prePost P mB := by
            apply integral_mono
            · rw [hμB]
              refine integrable_of_lin _ _ hmeas (|x - p₂|) 1 (fun q => ?_)
              rw [abs_of_nonneg (le_max_right _ _)]
              apply max_le _ (by positivity)
              have := le_abs_self (x - p₂); have := le_abs_self q; linarith
            · rw [hμB]; exact ((integrable_const _).add (integrable_sq_gauss _)).div_const _
            · intro q
              simp only
              apply max_le _ (by positivity)
              nlinarith [sq_nonneg (q - 1)]
        _ = (3 + (preVar P mB : ℝ)) / 2 := by
            rw [integral_div, hμB, integral_add (integrable_const _) (integrable_sq_gauss _),
              integral_sq_gauss]
            simp
        _ ≤ K := by rw [hK, Kc]; linarith
    have hdelay : ∀ x ∈ Icc (0 : ℝ) 1 \ B, x ≤ p₁ + d * K := by
      intro x hx
      have h := hdel x hx
      unfold DelaysPre at h
      have : (P.withδc d).δc = d := rfl
      rw [this] at h
      have := mul_le_mul_of_nonneg_left (hKb x hx.1.2) hd0
      have e1 : prePost (P.withδc d) mB = prePost P mB := rfl
      rw [e1] at h
      linarith
    set e := (volume (Icc θ₀ 1 \ B)).toReal with he_def
    have hfin : volume (Icc θ₀ 1 \ B) ≠ ⊤ :=
      ne_top_of_le_ne_top (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
        (measure_mono diff_subset)
    have he0 : 0 ≤ e := ENNReal.toReal_nonneg
    have he : e ≤ d * K := by
      apply ENNReal.toReal_le_of_le_ofReal hdK
      by_cases hp : p₁ ≤ 1
      · have hpθ : p₁ ≤ θ₀ := le_min (le_max_left _ _) hp
        calc volume (Icc θ₀ 1 \ B) ≤ volume (Icc θ₀ (p₁ + d * K)) := by
              apply measure_mono
              intro x ⟨hx, hxB⟩
              exact ⟨hx.1, hdelay x ⟨⟨le_trans hθ₀0 hx.1, hx.2⟩, hxB⟩⟩
          _ = ENNReal.ofReal (p₁ + d * K - θ₀) := Real.volume_Icc
          _ ≤ ENNReal.ofReal (d * K) := ENNReal.ofReal_le_ofReal (by linarith)
      · push_neg at hp
        have : θ₀ = 1 := by rw [hθ₀def]; exact min_eq_right (le_max_of_le_left hp.le)
        calc volume (Icc θ₀ 1 \ B) ≤ volume (Icc θ₀ 1) := measure_mono diff_subset
          _ = ENNReal.ofReal (1 - θ₀) := Real.volume_Icc
          _ ≤ ENNReal.ofReal (d * K) := ENNReal.ofReal_le_ofReal (by rw [this]; linarith)
    have hmBlow : 1 - θ₀ - e ≤ mB := by
      have h1 : volume (Icc θ₀ 1) ≤ volume B + volume (Icc θ₀ 1 \ B) := by
        calc volume (Icc θ₀ 1) ≤ volume (B ∪ (Icc θ₀ 1 \ B)) := by
              apply measure_mono; intro x hx
              by_cases hxB : x ∈ B
              · exact Or.inl hxB
              · exact Or.inr ⟨hx, hxB⟩
          _ ≤ _ := measure_union_le _ _
      have hBfin : volume B ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hvolB
      have h2 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hBfin, hfin⟩) h1
      rw [ENNReal.toReal_add hBfin hfin, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)] at h2
      rw [hmBdef]; unfold mass; linarith
    have hfirstK : (θ₀ - P.c) * mB ≤ (θ₀ - P.c) * (1 - θ₀) + d * K := by
      by_cases h : P.c ≤ θ₀
      · have := mul_le_mul_of_nonneg_left hmB1 (by linarith : (0:ℝ) ≤ θ₀ - P.c)
        linarith
      · push_neg at h
        have : (θ₀ - P.c) * (mB - (1 - θ₀)) ≤ e := by
          have h3 : (P.c - θ₀) * ((1 - θ₀) - mB) ≤ 1 * e :=
            mul_le_mul (by linarith) (by linarith) (by linarith) zero_le_one
          nlinarith
        nlinarith
    -- pointwise comparison of late masses
    have hpt : ∀ q, lateMass B p₂ q ≤ L θ₀ p₂ q + e := by
      intro q
      rw [← late_eq θ₀ hθ₀I]
      unfold lateMass
      have hsub : {x ∈ Icc (0 : ℝ) 1 \ B | p₂ ≤ x + q} ⊆
          {x ∈ Icc (0 : ℝ) 1 \ Icc θ₀ 1 | p₂ ≤ x + q} ∪ (Icc θ₀ 1 \ B) := by
        intro x ⟨⟨hx, hxB⟩, hxq⟩
        by_cases hxθ : x ∈ Icc θ₀ 1
        · exact Or.inr ⟨hxθ, hxB⟩
        · exact Or.inl ⟨⟨hx, hxθ⟩, hxq⟩
      have hA1 : volume {x ∈ Icc (0 : ℝ) 1 \ Icc θ₀ 1 | p₂ ≤ x + q} ≠ ⊤ :=
        ne_top_of_le_ne_top (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
          (measure_mono (fun x hx => hx.1.1) : _ ≤ volume (Icc (0 : ℝ) 1))
      have := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hA1, hfin⟩)
        (le_trans (measure_mono hsub) (measure_union_le _ _))
      rw [ENNReal.toReal_add hA1 hfin] at this
      exact this
    have hLint : Integrable (fun q => L θ₀ p₂ q) (prePost P mB) := by
      rw [hμB]; exact integrable_L _ θ₀ p₂ hθ₀0
    have hI1 : ∫ q, lateMass B p₂ q ∂prePost P mB ≤ ∫ q, L θ₀ p₂ q ∂prePost P mB + e := by
      calc ∫ q, lateMass B p₂ q ∂prePost P mB ≤ ∫ q, (L θ₀ p₂ q + e) ∂prePost P mB :=
            integral_mono hlm_int (hLint.add (integrable_const _)) hpt
        _ = _ := by
            rw [integral_add hLint (integrable_const _)]
            simp [hμB]
    have hgL : Continuous (fun q => L θ₀ p₂ q) :=
      continuous_L.comp (continuous_const.prodMk (continuous_const.prodMk continuous_id))
    have hI2 : ∫ q, L θ₀ p₂ q ∂prePost P mB ≤
        ∫ z, L θ₀ p₂ (sd P (1 - θ₀) * z) ∂gaussianReal 0 1 +
          Real.sqrt (P.σp ^ 2 * P.γ * (d * K)) := by
      rw [int_rep P hP mB hmB0 _ (measurable_L θ₀ p₂)]
      have h := lip_cmp (fun q => L θ₀ p₂ q) hgL (fun a b => L_lip θ₀ p₂ a b)
        (sd P mB) (sd P (1 - θ₀))
      have h2 := sd_lip P hP mB (1 - θ₀)
      have h3 : Real.sqrt (P.σp ^ 2 * P.γ * |mB - (1 - θ₀)|) ≤
          Real.sqrt (P.σp ^ 2 * P.γ * (d * K)) := by
        apply Real.sqrt_le_sqrt
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg (sq_nonneg _) hP.γ_nonneg)
        rw [abs_le]; constructor <;> linarith
      have := (abs_le.mp h).2
      linarith
    have hS : (p₂ - P.c) * ∫ q, lateMass B p₂ q ∂prePost P mB ≤
        (p₂ - P.c) * ∫ z, L θ₀ p₂ (sd P (1 - θ₀) * z) ∂gaussianReal 0 1 +
          (M - P.c) * (d * K + Real.sqrt (P.σp ^ 2 * P.γ * (d * K))) := by
      have hp2c : 0 ≤ p₂ - P.c := by linarith
      have h4 : ∫ q, lateMass B p₂ q ∂prePost P mB ≤
          ∫ z, L θ₀ p₂ (sd P (1 - θ₀) * z) ∂gaussianReal 0 1 +
            (d * K + Real.sqrt (P.σp ^ 2 * P.γ * (d * K))) := by linarith
      have h5 := mul_le_mul_of_nonneg_left h4 hp2c
      have h6 : (p₂ - P.c) * (d * K + Real.sqrt (P.σp ^ 2 * P.γ * (d * K))) ≤
          (M - P.c) * (d * K + Real.sqrt (P.σp ^ 2 * P.γ * (d * K))) :=
        mul_le_mul_of_nonneg_right (by linarith) (add_nonneg hdK (Real.sqrt_nonneg _))
      linarith
    have hFθ := hF θ₀ hθ₀I p₂ ⟨h1.le, h2⟩
    unfold Fh at hFθ
    have : (p₁ - P.c) * mB + (p₂ - P.c) * ∫ q, lateMass B p₂ q ∂prePost P mB ≤ Fm + errf P M d := by
      unfold errf; rw [← hK]; linarith
    exact le_trans this (le_trans (le_max_left _ _) (le_max_right _ _))

/-! ## Lower bound on responsive profits for small δc -/

noncomputable def Hh (P : Params) (ζ : ℝ) : ℝ := ∫ z, D P.c ζ ζ (sd P (1 - ζ) * z) ∂gaussianReal 0 1

lemma Hh_cont (P : Params) (hP : P.Standing) : ContinuousOn (Hh P) (Icc 0 1) := by
  unfold Hh
  have hsd : Continuous (fun x : ℝ => sd P (1 - x)) :=
    (continuous_sd P hP).comp (continuous_const.sub continuous_id)
  refine continuousOn_of_dominated (bound := fun _ => 1) ?_ ?_ (integrable_const _) ?_
  · intro x _
    exact ((continuous_D P.c).comp (continuous_const.prodMk (continuous_const.prodMk
      (continuous_const.mul continuous_id)))).aestronglyMeasurable
  · intro x hx
    refine ae_of_all _ (fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (D_nonneg _ _ _ _)]
    exact le_trans (D_le _ _ _ _ hx.1) hx.2
  · refine ae_of_all _ (fun z => Continuous.continuousOn ?_)
    exact (continuous_D P.c).comp (continuous_id.prodMk (continuous_id.prodMk
      (hsd.mul continuous_const)))

lemma measurable_D (c x θ : ℝ) : Measurable (fun q => D c x θ q) :=
  ((continuous_D c).comp (continuous_const.prodMk (continuous_const.prodMk continuous_id))).measurable

lemma integrable_D (v : ℝ≥0) (c x θ : ℝ) (hx : 0 ≤ x) :
    Integrable (fun q => D c x θ q) (gaussianReal 0 v) :=
  integrable_of_lin v _ (measurable_D c x θ) x 0 (fun q => by
    rw [abs_of_nonneg (D_nonneg _ _ _ _)]; simpa using D_le c x θ q hx)

lemma resp_lower (P : Params) (hP : P.Standing) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1)
    (d : ℝ) (hd0 : 0 ≤ d) (hd : d < 1 - p) :
    ∃ ζ ∈ Icc p (p + d), ((Rh P p ζ : ℝ) : EReal) ≤ respValue (P.withδc d) := by
  have hHnn : ∀ ζ, 0 ≤ Hh P ζ := fun ζ => integral_nonneg (fun z => D_nonneg _ _ _ _)
  have hHle : ∀ ζ ∈ Icc (0 : ℝ) 1, Hh P ζ ≤ 1 := by
    intro ζ hζ
    unfold Hh
    calc ∫ z, D P.c ζ ζ (sd P (1 - ζ) * z) ∂gaussianReal 0 1 ≤ ∫ z, (1 : ℝ) ∂gaussianReal 0 1 := by
          apply integral_mono _ (integrable_const _)
          · intro z; exact le_trans (D_le _ _ _ _ hζ.1) hζ.2
          · exact integrable_of_lin 1 _ ((measurable_D _ _ _).comp (measurable_const_mul _)) 1 0
              (fun z => by
                rw [abs_of_nonneg (D_nonneg _ _ _ _)]
                simpa using le_trans (D_le _ _ _ _ hζ.1) hζ.2)
      _ = 1 := by simp
  set φ := fun ζ => ζ - p - d * Hh P ζ with hφ
  have hφc : ContinuousOn φ (Icc p 1) :=
    ((continuousOn_id.sub continuousOn_const).sub (continuousOn_const.mul
      ((Hh_cont P hP).mono (Icc_subset_Icc hp0 le_rfl))))
  have h0mem : (0 : ℝ) ∈ Icc (φ p) (φ 1) := by
    constructor
    · simp only [hφ]; nlinarith [hHnn p]
    · simp only [hφ]; nlinarith [hHle 1 ⟨zero_le_one, le_rfl⟩, hHnn 1]
  obtain ⟨ζ, hζ, hφζ⟩ := intermediate_value_Icc hp1.le hφc h0mem
  simp only [hφ] at hφζ
  have hζI : ζ ∈ Icc (0 : ℝ) 1 := ⟨le_trans hp0 hζ.1, hζ.2⟩
  have hHζ := hHle ζ hζI
  have hd1 : d ≤ 1 := by linarith
  refine ⟨ζ, ⟨hζ.1, by nlinarith [hHnn ζ]⟩, ?_⟩
  set P' := P.withδc d with hP'def
  have hP' : P'.Standing := ⟨hP.σp_pos, hP.γ_nonneg, hd0, hd1, hP.c_nonneg, hP.c_lt_one⟩
  set s := fun q => SLPricing.Resp.p2Star P'.c q ζ with hs
  have hmass : mass (Icc ζ 1) = 1 - ζ := by
    unfold mass; rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith [hζ.2])]
  have hμ : prePost P' (mass (Icc ζ 1)) = gaussianReal 0 (preVar P (1 - ζ)) := by
    rw [hmass]; rfl
  have hint_eq : ∀ x, ∫ q, max (x + q - s q) 0 ∂prePost P' (mass (Icc ζ 1)) =
      ∫ q, D P.c x ζ q ∂gaussianReal 0 (preVar P (1 - ζ)) := by
    intro x
    rw [hμ]
    congr 1; funext q
    simp only [hs, D]
    rw [p2Star_eq _ _ _ hζI.1]; rfl
  have hHζ' : ∫ q, D P.c ζ ζ q ∂gaussianReal 0 (preVar P (1 - ζ)) = Hh P ζ := by
    unfold Hh
    exact int_rep P hP (1 - ζ) (by linarith [hζ.2]) _ (measurable_D _ _ _)
  have heq : IsRespEq P' p (Icc ζ 1) s := by
    refine ⟨measurableSet_Icc, fun x hx => ⟨le_trans hζI.1 hx.1, hx.2⟩, ?_, ?_, ?_, ?_⟩
    · simp only [hs]
      unfold SLPricing.Resp.p2Star
      refine Measurable.ite measurableSet_Iic measurable_const ?_
      refine Measurable.ite measurableSet_Iic ?_ measurable_id
      exact ((measurable_id.add_const _).add_const _).div_const _
    · intro q p₂
      exact (SLPricing.Compare.lemma_3 P' hP' (Icc ζ 1) ζ hζI rfl q).1 p₂
    · intro x hx
      unfold BuysEarlyResp
      refine ⟨by linarith [hx.1, hζ.1], ?_⟩
      rw [hint_eq x]
      have hx0 : 0 ≤ x := le_trans hζI.1 hx.1
      have hm : ∫ q, D P.c x ζ q ∂gaussianReal 0 (preVar P (1 - ζ)) ≤ Hh P ζ + (x - ζ) := by
        calc ∫ q, D P.c x ζ q ∂gaussianReal 0 (preVar P (1 - ζ))
            ≤ ∫ q, (D P.c ζ ζ q + (x - ζ)) ∂gaussianReal 0 (preVar P (1 - ζ)) := by
              apply integral_mono (integrable_D _ _ _ _ hx0)
                ((integrable_D _ _ _ _ hζI.1).add (integrable_const _))
              intro q; exact D_mono _ _ _ _ _ hx.1
          _ = _ := by
              rw [integral_add (integrable_D _ _ _ _ hζI.1) (integrable_const _), hHζ']
              simp
      have hdδ : P'.δc = d := rfl
      rw [hdδ]
      have := mul_le_mul_of_nonneg_left hm hd0
      have h2 : d * (x - ζ) ≤ x - ζ := by nlinarith [hx.1]
      linarith
    · intro x hx
      unfold DelaysResp
      rw [hint_eq x]
      have hxζ : x < ζ := by
        by_contra h; push_neg at h; exact hx.2 ⟨h, hx.1.2⟩
      have hx0 : 0 ≤ x := hx.1.1
      have hm : Hh P ζ ≤ ∫ q, D P.c x ζ q ∂gaussianReal 0 (preVar P (1 - ζ)) + (ζ - x) := by
        rw [← hHζ']
        calc ∫ q, D P.c ζ ζ q ∂gaussianReal 0 (preVar P (1 - ζ))
            ≤ ∫ q, (D P.c x ζ q + (ζ - x)) ∂gaussianReal 0 (preVar P (1 - ζ)) := by
              apply integral_mono (integrable_D _ _ _ _ hζI.1)
                ((integrable_D _ _ _ _ hx0).add (integrable_const _))
              intro q; exact D_mono _ _ _ _ _ hxζ.le
          _ = _ := by
              rw [integral_add (integrable_D _ _ _ _ hx0) (integrable_const _)]
              simp
      have hdδ : P'.δc = d := rfl
      rw [hdδ]
      have := mul_le_mul_of_nonneg_left hm hd0
      have h2 : d * (ζ - x) ≤ ζ - x := by nlinarith
      nlinarith
  have hprof : respProfit P' p (Icc ζ 1) s = Rh P p ζ := by
    unfold respProfit
    rw [Rh_eq P hP p ζ hζI.2, hmass]
    congr 1
    have : prePost P' (1 - ζ) = prePost P (1 - ζ) := rfl
    rw [this]
    congr 1; funext q
    simp only [hs]
    exact secondProfit_star P ζ hζI q
  rw [← hprof]
  exact le_iSup (fun o : {o : ℝ × Set ℝ × (ℝ → ℝ) // IsRespEq P' o.1 o.2.1 o.2.2} =>
    ((respProfit P' o.1.1 o.1.2.1 o.1.2.2 : ℝ) : EReal)) ⟨(p, Icc ζ 1, s), heq⟩

lemma errf_cont (P : Params) (M : ℝ) : Continuous (errf P M) := by
  unfold errf; fun_prop

lemma errf_zero (P : Params) (M : ℝ) : errf P M 0 = 0 := by
  simp [errf]

lemma Fh_zero (P : Params) (p₂ : ℝ) : Fh P 0 p₂ = -P.c := by
  simp [Fh, L_zero]

lemma Fh_one (P : Params) (hP : P.Standing) (p₂ : ℝ) : Fh P 1 p₂ ≤ (1 - P.c) ^ 2 / 4 := by
  have : Fh P 1 p₂ = (p₂ - P.c) * L 1 p₂ 0 := by
    simp [Fh, sd_zero]
  rw [this]
  have hc0 := hP.c_nonneg
  have hc1 := hP.c_lt_one
  rcases le_or_gt p₂ P.c with h | h
  · have := mul_nonpos_of_nonpos_of_nonneg (by linarith : p₂ - P.c ≤ 0) (L_nonneg 1 p₂ 0)
    nlinarith [sq_nonneg (1 - P.c)]
  · unfold L
    rw [sub_zero, max_eq_right (by linarith : (0:ℝ) ≤ p₂)]
    rcases le_or_gt p₂ 1 with h1 | h1
    · rw [max_eq_left (by linarith)]
      nlinarith [sq_nonneg (p₂ - P.c - (1 - p₂))]
    · rw [max_eq_right (by linarith)]
      nlinarith [sq_nonneg (1 - P.c)]

theorem main (P : Params) (hP : P.Standing) (hγ : 0 < P.γ) :
    ∃ T ∈ Ioc (0 : ℝ) 1, ∀ d ∈ Icc (0 : ℝ) T,
      preValue (P.withδc d) < respValue (P.withδc d) := by
  have hc0 := hP.c_nonneg
  have hc1 := hP.c_lt_one
  set Q := (1 - P.c) ^ 2 / 4 with hQ
  set η₀ := (1 - P.c) ^ 2 / 12 with hη₀
  have hη₀pos : 0 < η₀ := by rw [hη₀]; have : 0 < 1 - P.c := by linarith
                             positivity
  set M := max 2 (8 * P.σp ^ 2 / η₀) with hMdef
  have hM2 : 2 ≤ M := le_max_left _ _
  have hMpos : 0 < M := by linarith
  have h4M : 4 * P.σp ^ 2 / M ≤ η₀ / 2 := by
    rw [div_le_iff₀ hMpos]
    have h1 : 8 * P.σp ^ 2 / η₀ ≤ M := le_max_right _ _
    rw [div_le_iff₀ hη₀pos] at h1
    nlinarith
  -- maximize Fh over the compact box
  set Kset := Icc (0 : ℝ) 1 ×ˢ Icc P.c M with hKset
  have hKc : IsCompact Kset := isCompact_Icc.prod isCompact_Icc
  have hKne : Kset.Nonempty := ⟨(0, P.c), ⟨⟨le_rfl, zero_le_one⟩, ⟨le_rfl, by linarith⟩⟩⟩
  have hcont : ContinuousOn (fun x : ℝ × ℝ => Fh P x.1 x.2) Kset :=
    (Fh_cont P hP).mono (prod_mono subset_rfl (subset_univ _))
  obtain ⟨xs, hxsK, hmax⟩ := hKc.exists_isMaxOn hKne hcont
  set Fm := Fh P xs.1 xs.2 with hFm
  have hF : ∀ θ ∈ Icc (0 : ℝ) 1, ∀ p ∈ Icc P.c M, Fh P θ p ≤ Fm := by
    intro θ hθ p hp
    exact (isMaxOn_iff.mp hmax) (θ, p) ⟨hθ, hp⟩
  set X := max Fm (Q + η₀ / 2) with hX
  set p₀ := (2 + P.c) / 3 with hp₀
  have hR0 : Q + η₀ ≤ Rh P p₀ p₀ := by
    have := R_p0 P hP
    rw [hQ, hη₀]; rw [← hp₀] at this; linarith
  have hp₀I : p₀ ∈ Ico (0 : ℝ) 1 := ⟨by rw [hp₀]; linarith, by rw [hp₀]; linarith⟩
  have hchoose : ∃ p ∈ Ico (0 : ℝ) 1, X < Rh P p p := by
    have hθI := hxsK.1
    rcases eq_or_lt_of_le hθI.1 with h0 | h0
    · refine ⟨p₀, hp₀I, ?_⟩
      have : Fm = -P.c := by rw [hFm, ← h0, Fh_zero]
      rw [hX, max_lt_iff]; constructor
      · rw [this]; nlinarith [sq_nonneg (1 - P.c)]
      · linarith
    rcases eq_or_lt_of_le hθI.2 with h1 | h1
    · refine ⟨p₀, hp₀I, ?_⟩
      have : Fm ≤ Q := by rw [hFm, h1]; exact Fh_one P hP _
      rw [hX, max_lt_iff]; constructor <;> linarith
    · have hs := strict_gap P hP hγ xs.1 h0 h1 xs.2
      rw [← hFm] at hs
      by_cases hcmp : Rh P xs.1 xs.1 ≤ Rh P p₀ p₀
      · refine ⟨p₀, hp₀I, ?_⟩
        rw [hX, max_lt_iff]; constructor <;> linarith
      · refine ⟨xs.1, ⟨h0.le, h1⟩, ?_⟩
        rw [hX, max_lt_iff]; constructor <;> linarith
  obtain ⟨p, ⟨hp0, hp1⟩, hXp⟩ := hchoose
  set g := Rh P p p - X with hg
  have hgpos : 0 < g := by rw [hg]; linarith
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := Metric.continuousWithinAt_iff.mp
    ((Rh_cont P hP p) p ⟨hp0, hp1.le⟩) (g / 2) (by linarith)
  obtain ⟨δ₂, hδ₂, hδ₂'⟩ := Metric.continuousAt_iff.mp
    ((errf_cont P M).continuousAt (x := 0)) (g / 2) (by linarith)
  set T := min (min (δ₁ / 2) (δ₂ / 2)) (min ((1 - p) / 2) 1) with hT
  have hTpos : 0 < T := by
    rw [hT]
    apply lt_min (lt_min (by linarith) (by linarith)) (lt_min (by linarith) one_pos)
  have hT1 : T ≤ δ₁ / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hT2 : T ≤ δ₂ / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hT3 : T ≤ (1 - p) / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hT4 : T ≤ 1 := le_trans (min_le_right _ _) (min_le_right _ _)
  refine ⟨T, ⟨hTpos, hT4⟩, ?_⟩
  intro d ⟨hd0, hdT⟩
  -- pre-announced side
  have herr : errf P M d < g / 2 := by
    have h := hδ₂' (x := d) (by rw [Real.dist_eq, sub_zero, abs_of_nonneg hd0]; linarith)
    rw [errf_zero, Real.dist_eq, sub_zero] at h
    exact lt_of_le_of_lt (le_abs_self _) h
  have hpre : preValue (P.withδc d) ≤ ((X + g / 2 : ℝ) : EReal) := by
    unfold preValue
    refine iSup_le (fun o => ?_)
    rw [EReal.coe_le_coe_iff]
    refine le_trans (pre_bound P hP d hd0 M hM2 Fm hF o.1.1 o.1.2.1 o.1.2.2 o.2) ?_
    apply max_le
    · have : Q ≤ X := le_trans (by linarith) (le_max_right _ _)
      linarith
    apply max_le
    · have : Fm ≤ X := le_max_left _ _
      linarith
    · have : Q + η₀ / 2 ≤ X := le_max_right _ _
      linarith
  -- responsive side
  obtain ⟨ζ, hζ, hle⟩ := resp_lower P hP p hp0 hp1 d hd0 (by linarith)
  have hζI : ζ ∈ Icc (0 : ℝ) 1 := ⟨le_trans hp0 hζ.1, by linarith [hζ.2]⟩
  have hRζ : X + g / 2 < Rh P p ζ := by
    have h := hδ₁' (x := ζ) hζI (by
      rw [Real.dist_eq, abs_of_nonneg (by linarith [hζ.1])]; linarith [hζ.2])
    rw [Real.dist_eq] at h
    have := neg_abs_le (Rh P p ζ - Rh P p p)
    linarith
  calc preValue (P.withδc d) ≤ ((X + g / 2 : ℝ) : EReal) := hpre
    _ < ((Rh P p ζ : ℝ) : EReal) := EReal.coe_lt_coe_iff.mpr hRζ
    _ ≤ respValue (P.withδc d) := hle

end SLP8

open SLPricing.Compare in
theorem solution (P : Params) (hP : P.Standing) (hγ : 0 < P.γ) :
    ∃ T ∈ Ioc (0 : ℝ) 1, ∀ d ∈ Icc (0 : ℝ) T,
      preValue (P.withδc d) < respValue (P.withδc d) :=
  SLP8.main P hP hγ
