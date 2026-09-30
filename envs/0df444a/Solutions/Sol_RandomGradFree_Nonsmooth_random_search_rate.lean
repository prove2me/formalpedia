-- Prove2me | solution 1 for RandomGradFree.Nonsmooth.random_search_rate
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-29T23:52:54.658426+00:00
-- url     : https://prove2.me/submissions/0c9b928e-fb54-461b-affe-8d8fae20e0af

import Mathlib
import Definitions.Def_RandomGradFree_Nonsmooth_IsRandomSearchRun

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace RGF6



section gaussMoments

lemma gauss_mom2 (v : NNReal) : ∫ x, x ^ 2 ∂(gaussianReal 0 v) = v := by
  have hv := variance_fun_id_gaussianReal (μ := 0) (v := v)
  rw [variance_of_integral_eq_zero (by fun_prop) (by simp [integral_id_gaussianReal])] at hv
  exact hv

lemma hasDerivAt_expq (c t : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp (c * t ^ 2 / 2)) (c * t * Real.exp (c * t ^ 2 / 2)) t := by
  have := (((hasDerivAt_pow 2 t).const_mul c).div_const 2).exp
  convert this using 1; push_cast; ring

lemma gauss_mom4 (v : NNReal) : ∫ x, x ^ 4 ∂(gaussianReal 0 v) = 3 * (v : ℝ) ^ 2 := by
  have h0 : (0 : ℝ) ∈ interior (integrableExpSet id (gaussianReal 0 v)) := by
    simp [integrableExpSet_id_gaussianReal]
  have h := iteratedDeriv_mgf_zero h0 4
  rw [mgf_id_gaussianReal] at h
  set c : ℝ := (v : ℝ) with hc
  have e : (fun t : ℝ => Real.exp (0 * t + c * t ^ 2 / 2)) = fun t => Real.exp (c * t ^ 2 / 2) := by
    funext t; simp
  rw [e] at h
  have d1 : deriv (fun t : ℝ => Real.exp (c * t ^ 2 / 2)) = fun t => c * t * Real.exp (c * t ^ 2 / 2) := by
    funext t; exact (hasDerivAt_expq c t).deriv
  have d2 : deriv (fun t : ℝ => c * t * Real.exp (c * t ^ 2 / 2)) =
      fun t => (c + c ^ 2 * t ^ 2) * Real.exp (c * t ^ 2 / 2) := by
    funext t
    have hd : HasDerivAt (fun t : ℝ => c * t * Real.exp (c * t ^ 2 / 2))
        ((c + c ^ 2 * t ^ 2) * Real.exp (c * t ^ 2 / 2)) t := by
      have := ((hasDerivAt_id t).const_mul c).mul (hasDerivAt_expq c t)
      exact this.congr_deriv (by simp only [id, mul_one]; ring)
    exact hd.deriv
  have d3 : deriv (fun t : ℝ => (c + c ^ 2 * t ^ 2) * Real.exp (c * t ^ 2 / 2)) =
      fun t => (3 * c ^ 2 * t + c ^ 3 * t ^ 3) * Real.exp (c * t ^ 2 / 2) := by
    funext t
    have hd : HasDerivAt (fun t : ℝ => (c + c ^ 2 * t ^ 2) * Real.exp (c * t ^ 2 / 2))
        ((3 * c ^ 2 * t + c ^ 3 * t ^ 3) * Real.exp (c * t ^ 2 / 2)) t := by
      have := (((hasDerivAt_pow 2 t).const_mul (c ^ 2)).const_add c).mul (hasDerivAt_expq c t)
      exact this.congr_deriv (by push_cast; ring)
    exact hd.deriv
  have d4 : deriv (fun t : ℝ => (3 * c ^ 2 * t + c ^ 3 * t ^ 3) * Real.exp (c * t ^ 2 / 2)) =
      fun t => (3 * c ^ 2 + 6 * c ^ 3 * t ^ 2 + c ^ 4 * t ^ 4) * Real.exp (c * t ^ 2 / 2) := by
    funext t
    have hd : HasDerivAt (fun t : ℝ => (3 * c ^ 2 * t + c ^ 3 * t ^ 3) * Real.exp (c * t ^ 2 / 2))
        ((3 * c ^ 2 + 6 * c ^ 3 * t ^ 2 + c ^ 4 * t ^ 4) * Real.exp (c * t ^ 2 / 2)) t := by
      have := (((hasDerivAt_id t).const_mul (3 * c ^ 2)).add
        ((hasDerivAt_pow 3 t).const_mul (c ^ 3))).mul (hasDerivAt_expq c t)
      exact this.congr_deriv (by simp only [id, Pi.add_apply]; push_cast; ring)
    exact hd.deriv
  simp only [iteratedDeriv_succ, iteratedDeriv_zero, d1, d2, d3, d4] at h
  rw [show (∫ x, x ^ 4 ∂(gaussianReal 0 v)) = ∫ x, (id ^ 4) x ∂(gaussianReal 0 v) from rfl, ← h]
  simp

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

lemma integral_pi_gauss (g : (Fin N → ℝ) → ℝ) :
    ∫ y, g y ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1) =
      (Real.sqrt (2 * Real.pi))⁻¹ ^ N * ∫ y, gw y * g y := by
  have hm : Measurable (fun y : Fin N → ℝ => ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (y i))) :=
    ENNReal.measurable_ofReal.comp (Finset.measurable_prod _ fun i _ =>
      (measurable_gaussianPDFReal 0 1).comp (measurable_pi_apply i))
  rw [pi_gauss_eq, integral_withDensity_eq_integral_toReal_smul hm
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top), ← integral_const_mul]
  congr 1
  funext y
  rw [ENNReal.toReal_ofReal (Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg 0 1 _),
    prod_pdf, smul_eq_mul, mul_assoc]

end dens
end gaussMoments

section proj

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma proj_inner {Q : Set E} (hQ : Convex ℝ Q) {y z : E} (hz : z ∈ Q)
    (hmin : ∀ w ∈ Q, ‖y - z‖ ≤ ‖y - w‖) : ∀ w ∈ Q, inner ℝ (y - z) (w - z) ≤ 0 := by
  have h : ‖y - z‖ = ⨅ w : Q, ‖y - w‖ := by
    apply le_antisymm
    · have : Nonempty Q := ⟨⟨z, hz⟩⟩
      exact le_ciInf (fun w => hmin w w.2)
    · exact ciInf_le (show BddBelow (Set.range fun w : Q => ‖y - (w : E)‖) from
        ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩) (⟨z, hz⟩ : Q)
  exact (norm_eq_iInf_iff_real_inner_le_zero hQ hz).1 h

lemma proj_lip {Q : Set E} (hQ : Convex ℝ Q) {y1 y2 z1 z2 : E} (h1 : z1 ∈ Q)
    (m1 : ∀ w ∈ Q, ‖y1 - z1‖ ≤ ‖y1 - w‖) (h2 : z2 ∈ Q)
    (m2 : ∀ w ∈ Q, ‖y2 - z2‖ ≤ ‖y2 - w‖) : ‖z1 - z2‖ ≤ ‖y1 - y2‖ := by
  have a := proj_inner hQ h1 m1 z2 h2
  have b := proj_inner hQ h2 m2 z1 h1
  have e : inner ℝ (y1 - y2) (z1 - z2) = - inner ℝ (y1 - z1) (z2 - z1) - inner ℝ (y2 - z2) (z1 - z2)
      + ‖z1 - z2‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, real_inner_comm]
    ring
  have hle : inner ℝ (y1 - y2) (z1 - z2) ≤ ‖y1 - y2‖ * ‖z1 - z2‖ := real_inner_le_norm _ _
  by_cases hz : ‖z1 - z2‖ = 0
  · rw [hz]; exact norm_nonneg _
  · have hpos : 0 < ‖z1 - z2‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    have : ‖z1 - z2‖ * ‖z1 - z2‖ ≤ ‖y1 - y2‖ * ‖z1 - z2‖ := by nlinarith
    exact le_of_mul_le_mul_right this hpos

lemma proj_nonexp {Q : Set E} (hQ : Convex ℝ Q) {y z : E} (hz : z ∈ Q)
    (m : ∀ w ∈ Q, ‖y - z‖ ≤ ‖y - w‖) {w : E} (hw : w ∈ Q) : ‖z - w‖ ≤ ‖y - w‖ := by
  have := proj_inner hQ hz m w hw
  have e : ‖y - w‖ ^ 2 = ‖y - z‖ ^ 2 - 2 * inner ℝ (y - z) (w - z) + ‖z - w‖ ^ 2 := by
    have : y - w = (y - z) - (w - z) := by abel
    rw [this, norm_sub_sq_real, show ‖w - z‖ = ‖z - w‖ from norm_sub_rev _ _]
  have : ‖z - w‖ ^ 2 ≤ ‖y - w‖ ^ 2 := by nlinarith [sq_nonneg ‖y - z‖]
  by_contra hlt
  push_neg at hlt
  nlinarith [norm_nonneg (z - w), norm_nonneg (y - w)]

lemma proj_exists [FiniteDimensional ℝ E] {Q : Set E} (hc : IsClosed Q) (hne : Q.Nonempty)
    (y : E) : ∃ z ∈ Q, ∀ w ∈ Q, ‖y - z‖ ≤ ‖y - w‖ := by
  obtain ⟨z, hz, hd⟩ := hc.exists_infDist_eq_dist hne y
  refine ⟨z, hz, fun w hw => ?_⟩
  rw [← dist_eq_norm, ← dist_eq_norm, ← hd]
  exact Metric.infDist_le_dist_of_mem hw

lemma proj_fun [FiniteDimensional ℝ E] {Q : Set E} (hc : IsClosed Q) (hQ : Convex ℝ Q)
    (hne : Q.Nonempty) :
    ∃ π : E → E, Continuous π ∧ ∀ y, π y ∈ Q ∧ ∀ w ∈ Q, ‖y - π y‖ ≤ ‖y - w‖ := by
  choose π hπ using proj_exists hc hne
  refine ⟨π, ?_, fun y => hπ y⟩
  have : LipschitzWith 1 π := by
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    simp only [NNReal.coe_one, one_mul, dist_eq_norm]
    exact proj_lip hQ (hπ a).1 (hπ a).2 (hπ b).1 (hπ b).2
  exact this.continuous

end proj

section coord

variable {N : ℕ}

noncomputable abbrev gN (N : ℕ) : Measure (Fin N → ℝ) := Measure.pi fun _ : Fin N => gaussianReal 0 1

noncomputable def sg (y : Fin N → ℝ) : ℝ := ∑ i, |y i|

lemma sg_nonneg (y : Fin N → ℝ) : 0 ≤ sg y := Finset.sum_nonneg fun i _ => abs_nonneg _

lemma abs_le_sg (y : Fin N → ℝ) (i : Fin N) : |y i| ≤ sg y :=
  Finset.single_le_sum (f := fun j => |y j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)

lemma sg_add (y c : Fin N → ℝ) : sg (y + c) ≤ sg y + sg c := by
  unfold sg
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => abs_add_le (y i) (c i)

lemma sg_smul (t : ℝ) (w : Fin N → ℝ) : sg (t • w) = |t| * sg w := by
  unfold sg
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by simp [abs_mul]

lemma integrable_exp_sg (a : ℝ) :
    Integrable (fun y : Fin N → ℝ => Real.exp (a * sg y)) (gN N) := by
  have h1 : Integrable (fun x : ℝ => Real.exp (a * |x|)) (gaussianReal 0 1) := by
    refine ((integrable_exp_mul_gaussianReal (μ := 0) (v := 1) a).add
      (integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (-a))).mono' ?_ ?_
    · exact (by fun_prop : Measurable fun x : ℝ => Real.exp (a * |x|)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun x => ?_
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      rcases abs_cases x with ⟨h, _⟩ | ⟨h, _⟩
      · rw [h]; simp only [Pi.add_apply]
        exact le_add_of_nonneg_right (Real.exp_pos _).le
      · rw [h]; simp only [Pi.add_apply]
        have : a * -x = -a * x := by ring
        rw [this]
        exact le_add_of_nonneg_left (Real.exp_pos _).le
  have := Integrable.fintype_prod (μ := fun _ : Fin N => gaussianReal 0 1)
    (f := fun (_ : Fin N) (x : ℝ) => Real.exp (a * |x|)) (fun _ => h1)
  refine this.congr (Filter.Eventually.of_forall fun y => ?_)
  simp only [sg, Finset.mul_sum, Real.exp_sum]

lemma integrable_poly {G : (Fin N → ℝ) → ℝ} (hG : AEStronglyMeasurable G (gN N)) (C a : ℝ)
    (m : ℕ) (hC : 0 ≤ C)
    (h : ∀ y, |G y| ≤ C * (1 + sg y) ^ m * Real.exp (a * sg y)) : Integrable G (gN N) := by
  refine ((integrable_exp_sg (N := N) (a + 1)).const_mul
    (C * m.factorial * Real.exp 1)).mono' hG (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs]
  refine (h y).trans ?_
  have h1 : (1 + sg y) ^ m ≤ m.factorial * Real.exp (1 + sg y) := by
    have := Real.pow_div_factorial_le_exp (1 + sg y) (by linarith [sg_nonneg y]) m
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  have h2 : Real.exp (1 + sg y) * Real.exp (a * sg y) = Real.exp 1 * Real.exp ((a + 1) * sg y) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  calc C * (1 + sg y) ^ m * Real.exp (a * sg y)
      ≤ C * (m.factorial * Real.exp (1 + sg y)) * Real.exp (a * sg y) := by gcongr
    _ = C * m.factorial * (Real.exp (1 + sg y) * Real.exp (a * sg y)) := by ring
    _ = C * m.factorial * Real.exp 1 * Real.exp ((a + 1) * sg y) := by rw [h2]; ring

lemma pi_eval_int (i : Fin N) (g : ℝ → ℝ) (hg : Measurable g) :
    ∫ y, g (y i) ∂(gN N) = ∫ x, g x ∂(gaussianReal 0 1) := by
  have hm := measurePreserving_eval (fun _ : Fin N => gaussianReal 0 1) i
  rw [← hm.map_eq, integral_map hm.measurable.aemeasurable hg.aestronglyMeasurable]

lemma coord_sq (i : Fin N) : ∫ y, y i ^ 2 ∂(gN N) = 1 := by
  rw [pi_eval_int i (fun x => x ^ 2) (by fun_prop), gauss_mom2]; simp

lemma coord_4 (i : Fin N) : ∫ y, y i ^ 4 ∂(gN N) = 3 := by
  rw [pi_eval_int i (fun x => x ^ 4) (by fun_prop), gauss_mom4]; simp

lemma coord_1 (i : Fin N) : ∫ y, y i ∂(gN N) = 0 := by
  rw [pi_eval_int i (fun x => x) (by fun_prop), integral_id_gaussianReal]

lemma coord_22 {i j : Fin N} (hij : i ≠ j) : ∫ y, y i ^ 2 * y j ^ 2 ∂(gN N) = 1 := by
  have hind := iIndepFun_pi (μ := fun _ : Fin N => gaussianReal 0 1)
    (X := fun _ x => x) (fun _ => aemeasurable_id)
  have h2 := (hind.indepFun hij).comp (φ := fun x : ℝ => x ^ 2) (ψ := fun x : ℝ => x ^ 2)
    (by fun_prop) (by fun_prop)
  have := h2.integral_fun_mul_eq_mul_integral
    ((measurable_pi_apply i).pow_const 2).aestronglyMeasurable
    ((measurable_pi_apply j).pow_const 2).aestronglyMeasurable
  simp only [Function.comp_def] at this
  rw [this, coord_sq, coord_sq]; norm_num

lemma int_coord_prod (i j : Fin N) (p q : ℕ) :
    Integrable (fun y : Fin N → ℝ => y i ^ p * y j ^ q) (gN N) := by
  refine integrable_poly (a := 0) (m := p + q) (C := 1) (by fun_prop) zero_le_one ?_
  intro y
  rw [abs_mul, abs_pow, abs_pow, zero_mul, Real.exp_zero, mul_one, one_mul]
  have hi : |y i| ≤ 1 + sg y := by linarith [abs_le_sg y i]
  have hj : |y j| ≤ 1 + sg y := by linarith [abs_le_sg y j]
  have h0 : 0 ≤ 1 + sg y := by linarith [sg_nonneg y]
  calc |y i| ^ p * |y j| ^ q ≤ (1 + sg y) ^ p * (1 + sg y) ^ q :=
        mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hi p) (pow_le_pow_left₀ (abs_nonneg _) hj q)
          (by positivity) (pow_nonneg h0 p)
    _ = (1 + sg y) ^ (p + q) := by rw [pow_add]

lemma int_coord_pow (i : Fin N) (p : ℕ) : Integrable (fun y : Fin N → ℝ => y i ^ p) (gN N) := by
  simpa using int_coord_prod i i p 0

lemma sum_sq_sq : ∫ y, (∑ i, y i ^ 2) ^ 2 ∂(gN N) = (N : ℝ) ^ 2 + 2 * N := by
  have e : ∀ y : Fin N → ℝ, (∑ i, y i ^ 2) ^ 2 = ∑ i, ∑ j, y i ^ 2 * y j ^ 2 := by
    intro y; rw [sq, Finset.sum_mul_sum]
  simp_rw [e]
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ fun j _ => by
    simpa using int_coord_prod i j 2 2)]
  have : ∀ i : Fin N, ∫ y, ∑ j, y i ^ 2 * y j ^ 2 ∂(gN N) = (N : ℝ) + 2 := by
    intro i
    rw [integral_finset_sum _ (fun j _ => by simpa using int_coord_prod i j 2 2)]
    have : ∀ j : Fin N, ∫ y, y i ^ 2 * y j ^ 2 ∂(gN N) = 1 + if i = j then 2 else 0 := by
      intro j
      by_cases h : i = j
      · subst h; simp only [if_true]
        have := coord_4 (N := N) i
        rw [show (fun y : Fin N → ℝ => y i ^ 2 * y i ^ 2) = fun y => y i ^ 4 by
          funext y; ring, this]; norm_num
      · simp [h, coord_22 h]
    simp_rw [this]
    rw [Finset.sum_add_distrib]; simp
  simp_rw [this]
  simp; ring

end coord

section stein

variable {N : ℕ}

lemma cm_shift (Φ : (Fin N → ℝ) → ℝ) (c : Fin N → ℝ) :
    ∫ y, Φ (y + c) ∂(gN N) =
      ∫ y, Φ y * Real.exp (∑ i, c i * y i - (∑ i, c i ^ 2) / 2) ∂(gN N) := by
  rw [integral_pi_gauss, integral_pi_gauss]
  congr 1
  have h := integral_add_right_eq_self (μ := (volume : Measure (Fin N → ℝ)))
    (fun z => gw (z - c) * Φ z) c
  simp only [add_sub_cancel_right] at h
  rw [h]
  congr 1
  funext y
  have e : ∑ i, (y i - c i) ^ 2 = ∑ i, y i ^ 2 - 2 * ∑ i, c i * y i + ∑ i, c i ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have : gw (y - c) = gw y * Real.exp (∑ i, c i * y i - (∑ i, c i ^ 2) / 2) := by
    unfold gw
    rw [← Real.exp_add]
    congr 1
    simp only [Pi.sub_apply]
    rw [e]; ring
  rw [this]; ring

lemma stein_pi (Φ : (Fin N → ℝ) → ℝ) (hc : Continuous Φ) (hv : ConvexOn ℝ Set.univ Φ)
    (C K : ℝ) (hC : 0 ≤ C) (hK : 0 ≤ K) (hb : ∀ y, |Φ y| ≤ C + K * sg y) (w : Fin N → ℝ) :
    ∫ y, Φ y ∂(gN N) - ∫ y, Φ (y - w) ∂(gN N) ≤ ∫ y, Φ y * ∑ i, w i * y i ∂(gN N) := by
  have hint : ∀ c : Fin N → ℝ, Integrable (fun y => Φ (y + c)) (gN N) := by
    intro c
    have hA : 0 ≤ C + K * sg c := add_nonneg hC (mul_nonneg hK (sg_nonneg c))
    refine integrable_poly (a := 0) (m := 1) (C := (C + K * sg c) + K)
      (hc.comp (continuous_id.add continuous_const)).measurable.aestronglyMeasurable
      (add_nonneg hA hK) ?_
    intro y
    simp only [zero_mul, Real.exp_zero, mul_one, pow_one]
    calc |Φ (y + c)| ≤ C + K * sg (y + c) := hb _
      _ ≤ C + K * (sg y + sg c) := by gcongr; exact sg_add y c
      _ ≤ _ := by nlinarith [sg_nonneg y, sg_nonneg c]
  set W : ℝ := ∑ i, w i ^ 2 with hW
  set M : ℝ := ∑ i, |w i| with hM
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun i _ => abs_nonneg _
  set a : (Fin N → ℝ) → ℝ := fun y => ∑ i, w i * y i with ha
  have ha_cont : Continuous a := by simp only [ha]; fun_prop
  have ha_bd : ∀ y, |a y| ≤ M * sg y := by
    intro y
    calc |a y| ≤ ∑ i, |w i * y i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, |w i| * sg y := Finset.sum_le_sum fun i _ => by
            rw [abs_mul]; exact mul_le_mul_of_nonneg_left (abs_le_sg y i) (abs_nonneg _)
      _ = M * sg y := by rw [hM, Finset.sum_mul]
  let ψ : ℝ → ℝ := fun t => ∫ y, Φ (y + t • w) ∂(gN N)
  have hψconv : ConvexOn ℝ Set.univ ψ := by
    refine ⟨convex_univ, fun s _ t _ p q hp hq hpq => ?_⟩
    have pt : ∀ y : Fin N → ℝ, Φ (y + (p * s + q * t) • w) ≤
        p * Φ (y + s • w) + q * Φ (y + t • w) := by
      intro y
      have h := hv.2 (Set.mem_univ (y + s • w)) (Set.mem_univ (y + t • w)) hp hq hpq
      have e : y + (p * s + q * t) • w = p • (y + s • w) + q • (y + t • w) := by
        calc y + (p * s + q * t) • w = (p + q) • y + (p * s + q * t) • w := by rw [hpq, one_smul]
          _ = _ := by module
      rw [e]; simpa using h
    show ψ (p • s + q • t) ≤ p • ψ s + q • ψ t
    simp only [ψ, smul_eq_mul]
    calc ∫ y, Φ (y + (p * s + q * t) • w) ∂(gN N)
        ≤ ∫ y, (p * Φ (y + s • w) + q * Φ (y + t • w)) ∂(gN N) :=
          integral_mono (hint _) (((hint _).const_mul p).add ((hint _).const_mul q)) pt
      _ = _ := by
          rw [integral_add ((hint _).const_mul p) ((hint _).const_mul q), integral_const_mul,
            integral_const_mul]
  have hψexp : ∀ t, ψ t = ∫ y, Φ y * Real.exp (t * a y - t ^ 2 * W / 2) ∂(gN N) := by
    intro t
    simp only [ψ]
    rw [cm_shift]
    congr 1; funext y
    congr 2
    simp only [Pi.smul_apply, smul_eq_mul, ha, hW]
    have : ∑ i, (t * w i) ^ 2 = t ^ 2 * ∑ i, w i ^ 2 := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [this]
    have : ∑ i, t * w i * y i = t * ∑ i, w i * y i := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [this]
  let bnd : (Fin N → ℝ) → ℝ := fun y => (C + K * sg y) * Real.exp (M * sg y) * (M * sg y + W)
  have hbnd_meas : Continuous (fun y => bnd y) := by
    have : Continuous (fun y : Fin N → ℝ => sg y) := by simp only [sg]; fun_prop
    simp only [bnd]; fun_prop
  have hbnd_int : Integrable bnd (gN N) := by
    refine integrable_poly (a := M) (m := 2) (C := (C + K) * (M + W)) hbnd_meas.aestronglyMeasurable
      (mul_nonneg (add_nonneg hC hK) (add_nonneg hM0 hW0)) ?_
    intro y
    have hs := sg_nonneg y
    have e1 : C + K * sg y ≤ (C + K) * (1 + sg y) := by nlinarith
    have e2 : M * sg y + W ≤ (M + W) * (1 + sg y) := by nlinarith
    have hpos : 0 ≤ Real.exp (M * sg y) := (Real.exp_pos _).le
    have hb0 : 0 ≤ bnd y := by simp only [bnd]; positivity
    rw [abs_of_nonneg hb0]
    calc bnd y = ((C + K * sg y) * (M * sg y + W)) * Real.exp (M * sg y) := by simp only [bnd]; ring
      _ ≤ (((C + K) * (1 + sg y)) * ((M + W) * (1 + sg y))) * Real.exp (M * sg y) := by
          gcongr
      _ = _ := by ring
  have hderiv : HasDerivAt (fun t => ∫ y, Φ y * Real.exp (t * a y - t ^ 2 * W / 2) ∂(gN N))
      (∫ y, Φ y * a y ∂(gN N)) 0 := by
    have hmeas : ∀ t : ℝ, AEStronglyMeasurable (fun y => Φ y * Real.exp (t * a y - t ^ 2 * W / 2))
        (gN N) := by
      intro t
      exact (hc.mul (by fun_prop : Continuous fun y => Real.exp (t * a y - t ^ 2 * W / 2))).aestronglyMeasurable
    have hint0 : Integrable (fun y => Φ y * Real.exp ((0:ℝ) * a y - (0:ℝ) ^ 2 * W / 2)) (gN N) := by
      simpa using (by simpa using hint 0 : Integrable Φ (gN N))
    have hmeas' : AEStronglyMeasurable
        (fun y => Φ y * (Real.exp ((0:ℝ) * a y - (0:ℝ) ^ 2 * W / 2) * (a y - 0 * W))) (gN N) :=
      (hc.mul ((by fun_prop : Continuous fun y => Real.exp ((0:ℝ) * a y - (0:ℝ) ^ 2 * W / 2)).mul
        (ha_cont.sub continuous_const))).aestronglyMeasurable
    have hbd : ∀ᵐ y ∂(gN N), ∀ t ∈ Metric.ball (0:ℝ) 1,
        ‖Φ y * (Real.exp (t * a y - t ^ 2 * W / 2) * (a y - t * W))‖ ≤ bnd y := by
      refine Filter.Eventually.of_forall fun y t ht => ?_
      have ht' : |t| < 1 := by simpa using ht
      have hs := sg_nonneg y
      have hay := ha_bd y
      have hexp : Real.exp (t * a y - t ^ 2 * W / 2) ≤ Real.exp (M * sg y) := by
        apply Real.exp_le_exp.2
        have : t * a y ≤ |a y| := by
          calc t * a y ≤ |t * a y| := le_abs_self _
            _ = |t| * |a y| := abs_mul _ _
            _ ≤ 1 * |a y| := by gcongr
            _ = |a y| := one_mul _
        nlinarith [sq_nonneg t, mul_nonneg (sq_nonneg t) hW0]
      have hlin : |a y - t * W| ≤ M * sg y + W := by
        calc |a y - t * W| ≤ |a y| + |t * W| := abs_sub _ _
          _ ≤ M * sg y + W := by
              rw [abs_mul, abs_of_nonneg hW0]
              have : |t| * W ≤ 1 * W := by gcongr
              linarith
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
      have hΦ := hb y
      calc |Φ y| * (Real.exp (t * a y - t ^ 2 * W / 2) * |a y - t * W|)
          ≤ (C + K * sg y) * (Real.exp (M * sg y) * (M * sg y + W)) := by
            gcongr
        _ = bnd y := by simp only [bnd]; ring
    have hdiff : ∀ᵐ y ∂(gN N), ∀ t ∈ Metric.ball (0:ℝ) 1,
        HasDerivAt (fun t => Φ y * Real.exp (t * a y - t ^ 2 * W / 2))
          (Φ y * (Real.exp (t * a y - t ^ 2 * W / 2) * (a y - t * W))) t := by
      refine Filter.Eventually.of_forall fun y t _ => ?_
      have h1 : HasDerivAt (fun t : ℝ => t * a y - t ^ 2 * W / 2) (a y - t * W) t := by
        have := ((hasDerivAt_id t).mul_const (a y)).sub (((hasDerivAt_pow 2 t).mul_const W).div_const 2)
        refine this.congr_deriv ?_
        simp; ring
      exact (h1.exp.const_mul (Φ y))
    have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := gN N) (x₀ := (0:ℝ))
      (F := fun t y => Φ y * Real.exp (t * a y - t ^ 2 * W / 2))
      (F' := fun t y => Φ y * (Real.exp (t * a y - t ^ 2 * W / 2) * (a y - t * W)))
      (bound := bnd) (Metric.ball_mem_nhds (0:ℝ) zero_lt_one) (Filter.Eventually.of_forall hmeas) hint0 hmeas' hbd hbnd_int hdiff
    refine this.2.congr_deriv ?_
    congr 1; funext y; simp
  have hd : HasDerivAt ψ (∫ y, Φ y * a y ∂(gN N)) 0 := by
    have : ψ = fun t => ∫ y, Φ y * Real.exp (t * a y - t ^ 2 * W / 2) ∂(gN N) := funext hψexp
    rw [this]; exact hderiv
  have hs := hψconv.slope_le_of_hasDerivAt (Set.mem_univ (-1 : ℝ)) (Set.mem_univ 0) (by norm_num) hd
  rw [slope_def_field] at hs
  have h0 : ψ 0 = ∫ y, Φ y ∂(gN N) := by simp [ψ]
  have h1 : ψ (-1) = ∫ y, Φ (y - w) ∂(gN N) := by simp [ψ, sub_eq_add_neg]
  rw [h0, h1] at hs
  simpa using hs

end stein

section Eside

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- coordinates-to-vector map -/
noncomputable def Aop (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] : (Fin (Module.finrank ℝ E) → ℝ) → E :=
  fun y => ∑ i, y i • stdOrthonormalBasis ℝ E i

lemma stdG_def : stdGaussian E = (gN (Module.finrank ℝ E)).map (Aop E) := rfl

lemma Aop_cont : Continuous (Aop E) := by unfold Aop; fun_prop

lemma Aop_meas : Measurable (Aop E) := Aop_cont.measurable

lemma norm_Aop_le (y : Fin (Module.finrank ℝ E) → ℝ) : ‖Aop E y‖ ≤ sg y := by
  unfold Aop sg
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_smul, (stdOrthonormalBasis ℝ E).orthonormal.norm_eq_one i, mul_one, Real.norm_eq_abs]

lemma norm_Aop_sq (y : Fin (Module.finrank ℝ E) → ℝ) : ‖Aop E y‖ ^ 2 = ∑ i, y i ^ 2 := by
  have ho := orthonormal_iff_ite.mp (stdOrthonormalBasis ℝ E).orthonormal
  rw [← real_inner_self_eq_norm_sq]
  unfold Aop
  simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, ho, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma inner_Aop (y : Fin (Module.finrank ℝ E) → ℝ) (c : E) :
    inner ℝ (Aop E y) c = ∑ i, y i * inner ℝ (stdOrthonormalBasis ℝ E i) c := by
  unfold Aop
  simp only [sum_inner, real_inner_smul_left]

lemma Aop_repr (c : E) : Aop E (fun i => inner ℝ (stdOrthonormalBasis ℝ E i) c) = c :=
  (stdOrthonormalBasis ℝ E).sum_repr' c

lemma Aop_sub (y w : Fin (Module.finrank ℝ E) → ℝ) : Aop E (y - w) = Aop E y - Aop E w := by
  unfold Aop; simp [sub_smul, Finset.sum_sub_distrib]

lemma Aop_comb (p q : ℝ) (y1 y2 : Fin (Module.finrank ℝ E) → ℝ) :
    Aop E (p • y1 + q • y2) = p • Aop E y1 + q • Aop E y2 := by
  unfold Aop
  simp [add_smul, Finset.sum_add_distrib, Finset.smul_sum, smul_smul]

lemma int_E {G : E → ℝ} (hG : AEStronglyMeasurable G (stdGaussian E)) (C : ℝ) (m : ℕ)
    (hC : 0 ≤ C) (h : ∀ v, |G v| ≤ C * (1 + ‖v‖) ^ m) : Integrable G (stdGaussian E) := by
  rw [stdG_def] at hG ⊢
  refine (integrable_map_measure hG Aop_meas.aemeasurable).2 ?_
  refine integrable_poly (a := 0) (m := m) (C := C) (hG.comp_aemeasurable Aop_meas.aemeasurable)
    hC fun y => ?_
  rw [zero_mul, Real.exp_zero, mul_one]
  refine (h (Aop E y)).trans ?_
  gcongr
  exact norm_Aop_le y

lemma int_E_norm_pow (m : ℕ) : Integrable (fun v : E => ‖v‖ ^ m) (stdGaussian E) := by
  refine int_E (by fun_prop) 1 m zero_le_one fun v => ?_
  rw [abs_of_nonneg (by positivity), one_mul]
  gcongr; linarith

lemma int_E_id : Integrable (fun v : E => v) (stdGaussian E) := by
  have := int_E_norm_pow (E := E) 1
  simp only [pow_one] at this
  exact (integrable_norm_iff aestronglyMeasurable_id).1 this

lemma E_sq : ∫ v, ‖v‖ ^ 2 ∂(stdGaussian E) = Module.finrank ℝ E := by
  rw [stdG_def, integral_map Aop_meas.aemeasurable (by fun_prop)]
  simp_rw [norm_Aop_sq]
  rw [integral_finset_sum _ (fun i _ => int_coord_pow i 2)]
  simp [coord_sq]

lemma E_four : ∫ v, ‖v‖ ^ 4 ∂(stdGaussian E) =
    (Module.finrank ℝ E : ℝ) ^ 2 + 2 * Module.finrank ℝ E := by
  rw [stdG_def, integral_map Aop_meas.aemeasurable (by fun_prop)]
  have : ∀ y : Fin (Module.finrank ℝ E) → ℝ, ‖Aop E y‖ ^ 4 = (∑ i, y i ^ 2) ^ 2 := by
    intro y; rw [← norm_Aop_sq]; ring
  simp_rw [this]
  exact sum_sq_sq

lemma E_inner (c : E) : ∫ v, inner ℝ v c ∂(stdGaussian E) = 0 := by
  have := integral_inner (𝕜 := ℝ) (μ := stdGaussian E) (f := fun v : E => v) int_E_id c
  simp only [integral_id_stdGaussian, inner_zero_right] at this
  rw [← this]
  exact integral_congr_ae (Filter.Eventually.of_forall fun v => real_inner_comm _ _)

lemma E_norm_le : ∫ v, ‖v‖ ∂(stdGaussian E) ≤ Real.sqrt (Module.finrank ℝ E) := by
  set m := ∫ v, ‖v‖ ∂(stdGaussian E) with hm
  have h1 : Integrable (fun v : E => ‖v‖) (stdGaussian E) := by
    simpa using int_E_norm_pow (E := E) 1
  have h2 := int_E_norm_pow (E := E) 2
  have key : 0 ≤ ∫ v, (‖v‖ - m) ^ 2 ∂(stdGaussian E) := integral_nonneg fun v => sq_nonneg _
  have e : ∫ v, (‖v‖ - m) ^ 2 ∂(stdGaussian E) =
      ∫ v, ‖v‖ ^ 2 ∂(stdGaussian E) - 2 * m * ∫ v, ‖v‖ ∂(stdGaussian E) + m ^ 2 := by
    have : ∀ v : E, (‖v‖ - m) ^ 2 = ‖v‖ ^ 2 - 2 * m * ‖v‖ + m ^ 2 := fun v => by ring
    simp_rw [this]
    have i1 : Integrable (fun v : E => ‖v‖ ^ 2 - 2 * m * ‖v‖) (stdGaussian E) :=
      h2.sub (h1.const_mul _)
    have i2 : Integrable (fun v : E => 2 * m * ‖v‖) (stdGaussian E) := h1.const_mul _
    rw [integral_add i1 (integrable_const _), integral_sub h2 i2, integral_const_mul]
    simp
  rw [e, E_sq, ← hm] at key
  have hm0 : 0 ≤ m := integral_nonneg fun v => norm_nonneg _
  have : m ^ 2 ≤ (Module.finrank ℝ E : ℝ) := by nlinarith
  exact (le_abs_self m).trans (Real.abs_le_sqrt this)

lemma stein_E (F : E → ℝ) (hc : Continuous F) (hv : ConvexOn ℝ Set.univ F) (C K : ℝ)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hb : ∀ v, |F v| ≤ C + K * ‖v‖) (c : E) :
    ∫ v, F v ∂(stdGaussian E) - ∫ v, F (v - c) ∂(stdGaussian E) ≤
      ∫ v, F v * inner ℝ v c ∂(stdGaussian E) := by
  rw [stdG_def]
  have hFs : Continuous (fun v : E => F (v - c)) := hc.comp (continuous_id.sub continuous_const)
  have hFi : Continuous (fun v : E => F v * inner ℝ v c) :=
    hc.mul (continuous_id.inner continuous_const)
  rw [integral_map Aop_meas.aemeasurable hc.aestronglyMeasurable,
    integral_map Aop_meas.aemeasurable hFs.aestronglyMeasurable,
    integral_map Aop_meas.aemeasurable hFi.aestronglyMeasurable]
  have hΦv : ConvexOn ℝ Set.univ (fun y => F (Aop E y)) := by
    refine ⟨convex_univ, fun y1 _ y2 _ p q hp hq hpq => ?_⟩
    have h := hv.2 (Set.mem_univ (Aop E y1)) (Set.mem_univ (Aop E y2)) hp hq hpq
    simp only [smul_eq_mul] at h ⊢
    rw [Aop_comb]; exact h
  have := stein_pi (fun y => F (Aop E y)) (hc.comp Aop_cont) hΦv C K hC hK
    (fun y => (hb _).trans (by gcongr; exact norm_Aop_le y))
    (fun i => inner ℝ (stdOrthonormalBasis ℝ E i) c)
  have e1 : ∀ y : Fin (Module.finrank ℝ E) → ℝ,
      F (Aop E (y - fun i => inner ℝ (stdOrthonormalBasis ℝ E i) c)) = F (Aop E y - c) := by
    intro y; rw [Aop_sub, Aop_repr]
  have e2 : ∀ y : Fin (Module.finrank ℝ E) → ℝ,
      F (Aop E y) * ∑ i, (inner ℝ (stdOrthonormalBasis ℝ E i) c) * y i = F (Aop E y) * inner ℝ (Aop E y) c := by
    intro y; rw [inner_Aop]; congr 1; exact Finset.sum_congr rfl fun i _ => by ring
  simp only [e1, e2] at this
  exact this

end Eside

section Gpart

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

lemma f_cont (f : E → ℝ) (L₀ : ℝ) (hL₀ : 0 ≤ L₀) (hLip : ∀ x y, |f x - f y| ≤ L₀ * ‖x - y‖) :
    Continuous f := by
  have : LipschitzWith ⟨L₀, hL₀⟩ f := by
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    simp only [dist_eq_norm, Real.dist_eq]
    exact hLip a b
  exact this.continuous

lemma int_lin {F : E → ℝ} (hc : Continuous F) (C K : ℝ) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hb : ∀ v, |F v| ≤ C + K * ‖v‖) : Integrable F (stdGaussian E) := by
  refine int_E hc.aestronglyMeasurable (C + K) 1 (by positivity) fun v => ?_
  refine (hb v).trans ?_
  rw [pow_one]
  nlinarith [norm_nonneg v, mul_nonneg hC (norm_nonneg v)]

lemma f_shift_bound (f : E → ℝ) (L₀ : ℝ) (hLip : ∀ x y, |f x - f y| ≤ L₀ * ‖x - y‖) (μ : ℝ)
    (a v : E) : |f (a + μ • v)| ≤ |f a| + L₀ * |μ| * ‖v‖ := by
  have h1 := hLip (a + μ • v) a
  have h2 : ‖a + μ • v - a‖ = |μ| * ‖v‖ := by
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
  rw [h2] at h1
  have := abs_sub_abs_le_abs_sub (f (a + μ • v)) (f a)
  linarith

lemma conv_shift (f : E → ℝ) (hf : ConvexOn ℝ Set.univ f) (μ : ℝ) (a : E) :
    ConvexOn ℝ Set.univ (fun v : E => f (a + μ • v)) := by
  refine ⟨convex_univ, fun y1 _ y2 _ p q hp hq hpq => ?_⟩
  have h := hf.2 (Set.mem_univ (a + μ • y1)) (Set.mem_univ (a + μ • y2)) hp hq hpq
  have e : a + μ • (p • y1 + q • y2) = p • (a + μ • y1) + q • (a + μ • y2) := by
    calc a + μ • (p • y1 + q • y2) = (p + q) • a + μ • (p • y1 + q • y2) := by
          rw [hpq, one_smul]
      _ = p • (a + μ • y1) + q • (a + μ • y2) := by module
  simp only [smul_eq_mul] at h ⊢
  rw [e]
  exact h

lemma jensen_E (f : E → ℝ) (hf : ConvexOn ℝ Set.univ f) (L₀ : ℝ) (hL₀ : 0 ≤ L₀)
    (hLip : ∀ x y, |f x - f y| ≤ L₀ * ‖x - y‖) (μ : ℝ) (a : E) :
    f a ≤ ∫ v, f (a + μ • v) ∂(stdGaussian E) := by
  have hfc := f_cont f L₀ hL₀ hLip
  have hsm : Integrable (fun v : E => μ • v) (stdGaussian E) := (int_E_id (E := E)).smul μ
  have hi : Integrable (fun v : E => a + μ • v) (stdGaussian E) :=
    (integrable_const a).add hsm
  have hint : ∫ v, (a + μ • v) ∂(stdGaussian E) = a := by
    rw [integral_add (integrable_const a) hsm, integral_smul,
      integral_id_stdGaussian]
    simp
  have hgi : Integrable (f ∘ fun v : E => a + μ • v) (stdGaussian E) :=
    int_lin (hfc.comp (by fun_prop)) |f a| (L₀ * |μ|) (abs_nonneg _) (by positivity)
      (fun v => f_shift_bound f L₀ hLip μ a v)
  have := hf.map_integral_le hfc.continuousOn isClosed_univ
    (Filter.Eventually.of_forall fun _ => Set.mem_univ _) hi hgi
  rwa [hint] at this

noncomputable def Psi2 (f : E → ℝ) (μ : ℝ) (xs a v : E) : ℝ :=
  ((f (a + μ • v) - f a) / μ) * inner ℝ v (a - xs)

lemma G_lower (f : E → ℝ) (hf : ConvexOn ℝ Set.univ f) (L₀ : ℝ) (hL₀ : 0 ≤ L₀)
    (hLip : ∀ x y, |f x - f y| ≤ L₀ * ‖x - y‖) (μ : ℝ) (hμ : 0 < μ) (xs a : E) :
    f a - f xs - μ * L₀ * Real.sqrt (Module.finrank ℝ E) ≤
      ∫ v, Psi2 f μ xs a v ∂(stdGaussian E) := by
  have hfc := f_cont f L₀ hL₀ hLip
  have hK : 0 ≤ L₀ * |μ| := by positivity
  have hFc : Continuous (fun v : E => f (a + μ • v)) := hfc.comp (by fun_prop)
  have hFi : Integrable (fun v : E => f (a + μ • v)) (stdGaussian E) :=
    int_lin hFc |f a| (L₀ * |μ|) (abs_nonneg _) hK (fun v => f_shift_bound f L₀ hLip μ a v)
  have hinner : Integrable (fun v : E => inner ℝ v (a - xs)) (stdGaussian E) :=
    int_lin (by fun_prop) 0 ‖a - xs‖ le_rfl (norm_nonneg _)
      (fun v => by rw [zero_add, mul_comm]; exact abs_real_inner_le_norm v (a - xs))
  have hG1 : Integrable (fun v : E => f (a + μ • v) * inner ℝ v (a - xs)) (stdGaussian E) := by
    refine int_E (hFc.mul (by fun_prop)).aestronglyMeasurable
      ((|f a| + L₀ * |μ|) * ‖a - xs‖) 2 (by positivity) (fun v => ?_)
    rw [abs_mul]
    have h1 := f_shift_bound f L₀ hLip μ a v
    have h2 : |inner ℝ v (a - xs)| ≤ ‖v‖ * ‖a - xs‖ := abs_real_inner_le_norm v (a - xs)
    have t := norm_nonneg v
    have hA := abs_nonneg (f a)
    have hc := norm_nonneg (a - xs)
    have key : (|f a| + L₀ * |μ| * ‖v‖) * ‖v‖ ≤ (|f a| + L₀ * |μ|) * (1 + ‖v‖) ^ 2 := by
      nlinarith [mul_nonneg hA t, mul_nonneg hA (sq_nonneg ‖v‖), mul_nonneg hK t,
        mul_nonneg hK (sq_nonneg ‖v‖)]
    calc |f (a + μ • v)| * |inner ℝ v (a - xs)|
        ≤ (|f a| + L₀ * |μ| * ‖v‖) * (‖v‖ * ‖a - xs‖) :=
          mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      _ = ((|f a| + L₀ * |μ| * ‖v‖) * ‖v‖) * ‖a - xs‖ := by ring
      _ ≤ ((|f a| + L₀ * |μ|) * (1 + ‖v‖) ^ 2) * ‖a - xs‖ :=
          mul_le_mul_of_nonneg_right key hc
      _ = (|f a| + L₀ * |μ|) * ‖a - xs‖ * (1 + ‖v‖) ^ 2 := by ring
  have stein := stein_E (fun v : E => f (a + μ • v)) hFc (conv_shift f hf μ a) |f a|
    (L₀ * |μ|) (abs_nonneg _) hK (fun v => f_shift_bound f L₀ hLip μ a v) (μ⁻¹ • (a - xs))
  have e1 : ∀ v : E, f (a + μ • (v - μ⁻¹ • (a - xs))) = f (xs + μ • v) := fun v => by
    congr 1
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hμ.ne', one_smul]
    abel
  have e2 : ∀ v : E, f (a + μ • v) * inner ℝ v (μ⁻¹ • (a - xs))
      = μ⁻¹ * (f (a + μ • v) * inner ℝ v (a - xs)) := fun v => by
    rw [real_inner_smul_right]; ring
  simp only [e1, e2, integral_const_mul] at stein
  have e3 : ∀ v : E, Psi2 f μ xs a v =
      μ⁻¹ * (f (a + μ • v) * inner ℝ v (a - xs)) - (f a / μ) * inner ℝ v (a - xs) := by
    intro v; unfold Psi2; ring
  have hint : ∫ v, Psi2 f μ xs a v ∂(stdGaussian E)
      = μ⁻¹ * ∫ v, f (a + μ • v) * inner ℝ v (a - xs) ∂(stdGaussian E) := by
    simp_rw [e3]
    rw [integral_sub (hG1.const_mul _) (hinner.const_mul _), integral_const_mul,
      integral_const_mul, E_inner]
    ring
  have hJ := jensen_E f hf L₀ hL₀ hLip μ a
  have hnorm : Integrable (fun v : E => ‖v‖) (stdGaussian E) := by
    simpa using int_E_norm_pow (E := E) 1
  have hi2 : Integrable (fun v : E => f (xs + μ • v)) (stdGaussian E) :=
    int_lin (hfc.comp (by fun_prop)) |f xs| (L₀ * |μ|) (abs_nonneg _) hK
      (fun v => f_shift_bound f L₀ hLip μ xs v)
  have hUp : ∫ v, f (xs + μ • v) ∂(stdGaussian E) ≤ f xs + L₀ * μ * Real.sqrt (Module.finrank ℝ E) := by
    calc ∫ v, f (xs + μ • v) ∂(stdGaussian E)
        ≤ ∫ v, (f xs + L₀ * μ * ‖v‖) ∂(stdGaussian E) := by
          refine integral_mono hi2 ((integrable_const _).add (hnorm.const_mul _)) (fun v => ?_)
          have := hLip (xs + μ • v) xs
          rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hμ] at this
          have := le_abs_self (f (xs + μ • v) - f xs)
          simp only
          nlinarith
      _ = f xs + L₀ * μ * ∫ v, ‖v‖ ∂(stdGaussian E) := by
          rw [integral_add (integrable_const _) (hnorm.const_mul _), integral_const_mul]
          simp
      _ ≤ f xs + L₀ * μ * Real.sqrt (Module.finrank ℝ E) :=
          by
            have := mul_le_mul_of_nonneg_left (E_norm_le (E := E)) (show 0 ≤ L₀ * μ by positivity)
            linarith
  rw [hint]
  linarith

end Gpart

section Rpart

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

lemma indep_x_u {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (u x : ℕ → Ω → E) (T : ℕ → E → E → E) (hT : ∀ k, Continuous (fun p : E × E => T k p.1 p.2))
    (x₀ : E) (hu : ∀ k, Measurable (u k)) (hind : iIndepFun u P)
    (h0 : x 0 = fun _ => x₀) (hs : ∀ k ω, x (k + 1) ω = T k (x k ω) (u k ω)) (k : ℕ) :
    Measurable (x k) ∧ IndepFun (x k) (u k) P := by
  let M : ℕ → MeasurableSpace Ω := fun k =>
    ⨆ i ∈ {i : ℕ | i < k}, MeasurableSpace.comap (u i) inferInstance
  have hMle : ∀ k, M k ≤ mΩ := fun k => iSup₂_le fun i _ => (hu i).comap_le
  have hMmono : ∀ k, M k ≤ M (k + 1) := fun k =>
    iSup₂_le fun i hi => le_iSup₂_of_le i (Nat.lt_succ_of_lt hi) le_rfl
  have hui : ∀ k, Measurable[M (k + 1)] (u k) := fun k =>
    Measurable.mono (comap_measurable (u k)) (le_iSup₂_of_le k (Nat.lt_succ_self k) le_rfl) le_rfl
  have hxm : ∀ k, Measurable[M k] (x k) := by
    intro k
    induction k with
    | zero => rw [h0]; exact measurable_const
    | succ k ih =>
      have h1 : Measurable[M (k + 1)] (x k) := ih.mono (hMmono k) le_rfl
      have h2 : Measurable[M (k + 1)] (fun ω => (x k ω, u k ω)) := h1.prodMk (hui k)
      have hx' : x (k + 1) = (fun p : E × E => T k p.1 p.2) ∘ (fun ω => (x k ω, u k ω)) := by
        funext ω; exact hs k ω
      rw [hx']
      exact (hT k).measurable.comp h2
  refine ⟨(hxm k).mono (hMle k) le_rfl, ?_⟩
  have hI : Indep (M k) (⨆ i ∈ ({k} : Set ℕ), MeasurableSpace.comap (u i) inferInstance) P :=
    indep_iSup_of_disjoint (m := fun i => MeasurableSpace.comap (u i) inferInstance)
      (fun i => (hu i).comap_le) hind (Set.disjoint_singleton_right.2 (fun h => lt_irrefl k h))
  have hle1 : MeasurableSpace.comap (x k) inferInstance ≤ M k := (hxm k).comap_le
  have hle2 : MeasurableSpace.comap (u k) inferInstance ≤
      ⨆ i ∈ ({k} : Set ℕ), MeasurableSpace.comap (u i) inferInstance :=
    le_iSup₂_of_le k rfl le_rfl
  exact indep_of_indep_of_le_left (indep_of_indep_of_le_right hI hle2) hle1

lemma indep_int {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → E} (hX : Measurable X) (hY : Measurable Y) (hI : IndepFun X Y P)
    (Ψ : E → E → ℝ) (hΨ : Continuous (fun p : E × E => Ψ p.1 p.2))
    (hint : Integrable (fun ω => Ψ (X ω) (Y ω)) P) :
    Integrable (fun a => ∫ v, Ψ a v ∂(P.map Y)) (P.map X) ∧
    ∫ ω, Ψ (X ω) (Y ω) ∂P = ∫ a, (∫ v, Ψ a v ∂(P.map Y)) ∂(P.map X) := by
  have hm : P.map (fun ω => (X ω, Y ω)) = (P.map X).prod (P.map Y) :=
    (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).1 hI
  have hpm : Measurable (fun ω => (X ω, Y ω)) := hX.prodMk hY
  have hprod : Integrable (fun p : E × E => Ψ p.1 p.2) ((P.map X).prod (P.map Y)) := by
    rw [← hm]
    exact (integrable_map_measure hΨ.aestronglyMeasurable hpm.aemeasurable).2 hint
  refine ⟨hprod.integral_prod_left, ?_⟩
  have h2 : ∫ ω, Ψ (X ω) (Y ω) ∂P = ∫ p : E × E, Ψ p.1 p.2 ∂((P.map X).prod (P.map Y)) := by
    rw [← hm, integral_map hpm.aemeasurable hΨ.aestronglyMeasurable]
  rw [h2]
  exact integral_prod _ hprod

lemma pt_ineq (f : E → ℝ) (L₀ : ℝ) (hL₀ : 0 ≤ L₀)
    (hLip : ∀ x y, |f x - f y| ≤ L₀ * ‖x - y‖) (μ : ℝ) (hμ : 0 < μ) (hk : ℝ) (xs a v z : E)
    (hz : ‖z - xs‖ ≤ ‖a - hk • (((f (a + μ • v) - f a) / μ) • v) - xs‖) :
    ‖z - xs‖ ^ 2 ≤ ‖a - xs‖ ^ 2 - 2 * hk * Psi2 f μ xs a v + hk ^ 2 * L₀ ^ 2 * ‖v‖ ^ 4 := by
  obtain ⟨g, hg⟩ : ∃ g : ℝ, g = (f (a + μ • v) - f a) / μ := ⟨_, rfl⟩
  rw [← hg] at hz
  have hgb : |g| ≤ L₀ * ‖v‖ := by
    have h1 := hLip (a + μ • v) a
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hμ] at h1
    rw [hg, abs_div, abs_of_pos hμ, div_le_iff₀ hμ]
    linarith
  have h1 : ‖z - xs‖ ^ 2 ≤ ‖a - hk • (g • v) - xs‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz 2
  have h2 : a - hk • (g • v) - xs = (a - xs) - (hk * g) • v := by rw [smul_smul]; abel
  have h3 : ‖(a - xs) - (hk * g) • v‖ ^ 2 =
      ‖a - xs‖ ^ 2 - 2 * (hk * g) * inner ℝ (a - xs) v + (hk * g) ^ 2 * ‖v‖ ^ 2 := by
    rw [norm_sub_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]; ring
  have h4 : g ^ 2 ≤ L₀ ^ 2 * ‖v‖ ^ 2 := by
    calc g ^ 2 = |g| ^ 2 := (sq_abs g).symm
      _ ≤ (L₀ * ‖v‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hgb 2
      _ = L₀ ^ 2 * ‖v‖ ^ 2 := by ring
  have h5 : Psi2 f μ xs a v = g * inner ℝ (a - xs) v := by
    unfold Psi2; rw [← hg, real_inner_comm]
  have h6 : (hk * g) ^ 2 * ‖v‖ ^ 2 ≤ hk ^ 2 * L₀ ^ 2 * ‖v‖ ^ 4 := by
    calc (hk * g) ^ 2 * ‖v‖ ^ 2 = (hk ^ 2 * ‖v‖ ^ 2) * g ^ 2 := by ring
      _ ≤ (hk ^ 2 * ‖v‖ ^ 2) * (L₀ ^ 2 * ‖v‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = hk ^ 2 * L₀ ^ 2 * ‖v‖ ^ 4 := by ring
  rw [h2, h3] at h1
  rw [h5]
  linarith

lemma step_lemma {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : E → ℝ) (hf : ConvexOn ℝ Set.univ f) (L₀ : ℝ) (hL₀ : 0 ≤ L₀)
    (hLip : ∀ x y, |f x - f y| ≤ L₀ * ‖x - y‖) (xs : E) (μ : ℝ) (hμ : 0 < μ) (hk : ℝ)
    (hk0 : 0 ≤ hk)
    (X Y Z : Ω → E) (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (hI : IndepFun X Y P) (hlaw : P.map Y = stdGaussian E)
    (hr : Integrable (fun ω => ‖X ω - xs‖ ^ 2) P)
    (hZle : ∀ ω, ‖Z ω - xs‖ ≤
      ‖X ω - hk • (((f (X ω + μ • Y ω) - f (X ω)) / μ) • Y ω) - xs‖) :
    Integrable (fun ω => ‖Z ω - xs‖ ^ 2) P ∧ Integrable (fun ω => f (X ω)) P ∧
    ∫ ω, ‖Z ω - xs‖ ^ 2 ∂P ≤ ∫ ω, ‖X ω - xs‖ ^ 2 ∂P
      - 2 * hk * (∫ ω, f (X ω) ∂P - f xs - μ * L₀ * Real.sqrt (Module.finrank ℝ E))
      + hk ^ 2 * L₀ ^ 2 * ((Module.finrank ℝ E : ℝ) + 4) ^ 2 := by
  have hfc := f_cont f L₀ hL₀ hLip
  have hn0 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  have hXs : Integrable (fun ω => ‖X ω - xs‖) P := by
    have hb : Integrable (fun ω => 1 + ‖X ω - xs‖ ^ 2) P := (integrable_const (1 : ℝ)).add hr
    refine hb.mono' ((hX.sub_const xs).norm.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    nlinarith [sq_nonneg (‖X ω - xs‖ - 1)]
  have hfX : Integrable (fun ω => f (X ω)) P := by
    have hb : Integrable (fun ω => |f xs| + L₀ * ‖X ω - xs‖) P :=
      (integrable_const _).add (hXs.const_mul L₀)
    refine hb.mono' (hfc.measurable.comp hX).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    have h1 := hLip (X ω) xs
    have h2 := abs_sub_abs_le_abs_sub (f (X ω)) (f xs)
    linarith
  have hYint : ∀ m : ℕ, Integrable (fun ω => ‖Y ω‖ ^ m) P := fun m => by
    have h := int_E_norm_pow (E := E) m
    rw [← hlaw] at h
    exact (integrable_map_measure h.aestronglyMeasurable hY.aemeasurable).1 h
  have hY4 : ∫ ω, ‖Y ω‖ ^ 4 ∂P = (Module.finrank ℝ E : ℝ) ^ 2 + 2 * Module.finrank ℝ E := by
    have := integral_map (μ := P) hY.aemeasurable (f := fun v : E => ‖v‖ ^ 4)
      (continuous_norm.pow 4).aestronglyMeasurable
    rw [hlaw, E_four] at this
    exact this.symm
  have hΨc : Continuous (fun p : E × E => Psi2 f μ xs p.1 p.2) := by
    have h1 : Continuous fun p : E × E => f (p.1 + μ • p.2) :=
      hfc.comp (continuous_fst.add (continuous_const.smul continuous_snd))
    have h2 : Continuous fun p : E × E => f p.1 := hfc.comp continuous_fst
    exact ((h1.sub h2).div_const μ).mul (continuous_snd.inner (continuous_fst.sub continuous_const))
  have hΨb : ∀ a v : E, |Psi2 f μ xs a v| ≤ L₀ * (‖v‖ ^ 2 * ‖a - xs‖) := by
    intro a v
    unfold Psi2
    have hg : |(f (a + μ • v) - f a) / μ| ≤ L₀ * ‖v‖ := by
      have h1 := hLip (a + μ • v) a
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hμ] at h1
      rw [abs_div, abs_of_pos hμ, div_le_iff₀ hμ]
      linarith
    have h2 : |inner ℝ v (a - xs)| ≤ ‖v‖ * ‖a - xs‖ := abs_real_inner_le_norm v (a - xs)
    rw [abs_mul]
    calc _ ≤ (L₀ * ‖v‖) * (‖v‖ * ‖a - xs‖) := mul_le_mul hg h2 (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hΨm : Measurable (fun ω => Psi2 f μ xs (X ω) (Y ω)) :=
    hΨc.measurable.comp (hX.prodMk hY)
  have hΨint : Integrable (fun ω => Psi2 f μ xs (X ω) (Y ω)) P := by
    have hind2 : IndepFun (fun ω => ‖Y ω‖ ^ 2) (fun ω => ‖X ω - xs‖) P :=
      hI.symm.comp (φ := fun v : E => ‖v‖ ^ 2) (ψ := fun a : E => ‖a - xs‖)
        (measurable_norm.pow_const 2) (measurable_id.sub_const xs).norm
    have hprodI : Integrable (fun ω => ‖Y ω‖ ^ 2 * ‖X ω - xs‖) P :=
      hind2.integrable_mul (hYint 2) hXs
    refine (hprodI.const_mul L₀).mono' hΨm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    exact hΨb _ _
  have hpt : ∀ ω, ‖Z ω - xs‖ ^ 2 ≤ ‖X ω - xs‖ ^ 2 - 2 * hk * Psi2 f μ xs (X ω) (Y ω)
      + hk ^ 2 * L₀ ^ 2 * ‖Y ω‖ ^ 4 :=
    fun ω => pt_ineq f L₀ hL₀ hLip μ hμ hk xs (X ω) (Y ω) (Z ω) (hZle ω)
  have hRf : Integrable (fun ω => ‖X ω - xs‖ ^ 2 - 2 * hk * Psi2 f μ xs (X ω) (Y ω)
      + hk ^ 2 * L₀ ^ 2 * ‖Y ω‖ ^ 4) P :=
    (hr.sub (hΨint.const_mul (2 * hk))).add ((hYint 4).const_mul _)
  have hZm : Measurable (fun ω => ‖Z ω - xs‖ ^ 2) := (hZ.sub_const xs).norm.pow_const 2
  have hZint : Integrable (fun ω => ‖Z ω - xs‖ ^ 2) P :=
    hRf.mono' hZm.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hpt ω)
  obtain ⟨hIint, hInt⟩ := indep_int P hX hY hI (Psi2 f μ xs) hΨc hΨint
  rw [hlaw] at hIint hInt
  have hlbc : Continuous (fun a : E => f a - f xs - μ * L₀ * Real.sqrt (Module.finrank ℝ E)) :=
    (hfc.sub continuous_const).sub continuous_const
  have hlbi : Integrable (fun a : E => f a - f xs - μ * L₀ * Real.sqrt (Module.finrank ℝ E))
      (P.map X) := by
    refine (integrable_map_measure hlbc.aestronglyMeasurable hX.aemeasurable).2 ?_
    exact (hfX.sub (integrable_const _)).sub (integrable_const _)
  have hlb : ∫ ω, (f (X ω) - f xs - μ * L₀ * Real.sqrt (Module.finrank ℝ E)) ∂P ≤
      ∫ ω, Psi2 f μ xs (X ω) (Y ω) ∂P := by
    rw [hInt]
    calc ∫ ω, (f (X ω) - f xs - μ * L₀ * Real.sqrt (Module.finrank ℝ E)) ∂P
        = ∫ a, (f a - f xs - μ * L₀ * Real.sqrt (Module.finrank ℝ E)) ∂(P.map X) :=
          (integral_map hX.aemeasurable hlbc.aestronglyMeasurable).symm
      _ ≤ ∫ a, ∫ v, Psi2 f μ xs a v ∂(stdGaussian E) ∂(P.map X) :=
          integral_mono hlbi hIint (fun a => G_lower f hf L₀ hL₀ hLip μ hμ xs a)
  have hE : ∫ ω, (f (X ω) - f xs - μ * L₀ * Real.sqrt (Module.finrank ℝ E)) ∂P
      = ∫ ω, f (X ω) ∂P - f xs - μ * L₀ * Real.sqrt (Module.finrank ℝ E) := by
    have i1 : Integrable (fun ω => f (X ω) - f xs) P := hfX.sub (integrable_const _)
    rw [integral_sub i1 (integrable_const _), integral_sub hfX (integrable_const _)]
    simp
  rw [hE] at hlb
  have hI2 : ∫ ω, ‖Z ω - xs‖ ^ 2 ∂P ≤ ∫ ω, (‖X ω - xs‖ ^ 2 - 2 * hk * Psi2 f μ xs (X ω) (Y ω)
      + hk ^ 2 * L₀ ^ 2 * ‖Y ω‖ ^ 4) ∂P := integral_mono hZint hRf hpt
  have hRfI : ∫ ω, (‖X ω - xs‖ ^ 2 - 2 * hk * Psi2 f μ xs (X ω) (Y ω)
      + hk ^ 2 * L₀ ^ 2 * ‖Y ω‖ ^ 4) ∂P = ∫ ω, ‖X ω - xs‖ ^ 2 ∂P
        - 2 * hk * ∫ ω, Psi2 f μ xs (X ω) (Y ω) ∂P
        + hk ^ 2 * L₀ ^ 2 * ∫ ω, ‖Y ω‖ ^ 4 ∂P := by
    have j1 : Integrable (fun ω => 2 * hk * Psi2 f μ xs (X ω) (Y ω)) P := hΨint.const_mul _
    have j2 : Integrable (fun ω => ‖X ω - xs‖ ^ 2 - 2 * hk * Psi2 f μ xs (X ω) (Y ω)) P :=
      hr.sub j1
    have j3 : Integrable (fun ω => hk ^ 2 * L₀ ^ 2 * ‖Y ω‖ ^ 4) P := (hYint 4).const_mul _
    rw [integral_add j2 j3, integral_sub hr j1, integral_const_mul, integral_const_mul]
  refine ⟨hZint, hfX, ?_⟩
  rw [hRfI, hY4] at hI2
  have h6 : hk ^ 2 * L₀ ^ 2 * ((Module.finrank ℝ E : ℝ) ^ 2 + 2 * Module.finrank ℝ E) ≤
      hk ^ 2 * L₀ ^ 2 * ((Module.finrank ℝ E : ℝ) + 4) ^ 2 :=
    mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
  have h7 := mul_le_mul_of_nonneg_left hlb (show 0 ≤ 2 * hk by positivity)
  linarith

end Rpart

end RGF6

open MeasureTheory ProbabilityTheory RandomGradFree.Nonsmooth in
theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (Q : Set E) (hQc : IsClosed Q) (hQconv : Convex ℝ Q)
    (f : E → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (L₀ : ℝ) (hL₀ : 0 ≤ L₀) (hLip : ∀ x y, |f x - f y| ≤ L₀ * ‖x - y‖)
    (xstar : E) (hxstar : xstar ∈ Q) (hopt : ∀ y ∈ Q, f xstar ≤ f y)
    (μ : ℝ) (hμ : 0 < μ) (h : ℕ → ℝ) (hh : ∀ k, 0 < h k) (x₀ : E)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (u : ℕ → Ω → E) (x : ℕ → Ω → E) (hrun : IsRandomSearchRun P Q f μ h x₀ u x) (N : ℕ) :
    (1 / ∑ k ∈ Finset.range (N + 1), h k) *
        ∑ k ∈ Finset.range (N + 1), h k * ((∫ ω, f (x k ω) ∂P) - f xstar)
      ≤ μ * L₀ * Real.sqrt (Module.finrank ℝ E)
        + (1 / ∑ k ∈ Finset.range (N + 1), h k) *
          (1 / 2 * ‖x₀ - xstar‖ ^ 2
            + ((Module.finrank ℝ E : ℝ) + 4) ^ 2 / 2 * L₀ ^ 2
              * ∑ k ∈ Finset.range (N + 1), h k ^ 2) := by
  obtain ⟨π, hπc, hπ⟩ := RGF6.proj_fun hQc hQconv ⟨xstar, hxstar⟩
  have hfc := RGF6.f_cont f L₀ hL₀ hLip
  let T : ℕ → E → E → E := fun k a v => π (a - h k • (((f (a + μ • v) - f a) / μ) • v))
  have hT : ∀ k, Continuous (fun p : E × E => T k p.1 p.2) := by
    intro k
    have h1 : Continuous fun p : E × E => f (p.1 + μ • p.2) :=
      hfc.comp (continuous_fst.add (continuous_const.smul continuous_snd))
    have h2 : Continuous fun p : E × E => f p.1 := hfc.comp continuous_fst
    have h3 : Continuous fun p : E × E =>
        p.1 - h k • (((f (p.1 + μ • p.2) - f p.1) / μ) • p.2) :=
      continuous_fst.sub (continuous_const.smul (((h1.sub h2).div_const μ).smul continuous_snd))
    exact hπc.comp h3
  have hxQ : ∀ k ω, x k ω ∈ Q := by
    intro k ω
    cases k with
    | zero => rw [hrun.init]; exact hrun.start_mem
    | succ k => exact (hrun.step k ω).1
  have hs : ∀ k ω, x (k + 1) ω = T k (x k ω) (u k ω) := by
    intro k ω
    have h1 := hrun.step k ω
    have h2 := hπ (x k ω - h k • (((f (x k ω + μ • u k ω) - f (x k ω)) / μ) • u k ω))
    have := RGF6.proj_lip hQconv h1.1 h1.2 h2.1 h2.2
    refine sub_eq_zero.1 (norm_le_zero_iff.1 (this.trans (le_of_eq ?_)))
    simp [oracle]
  have hu := hrun.measurable_dir
  obtain hxm := fun k => (RGF6.indep_x_u P u x T hT x₀ hu hrun.indep_dir hrun.init hs k)
  set n : ℝ := (Module.finrank ℝ E : ℝ) with hn
  set D : ℝ := μ * L₀ * Real.sqrt n with hD
  have hgen : ∀ k, Integrable (fun ω => ‖x k ω - xstar‖ ^ 2) P →
      Integrable (fun ω => ‖x (k + 1) ω - xstar‖ ^ 2) P ∧ Integrable (fun ω => f (x k ω)) P ∧
      ∫ ω, ‖x (k + 1) ω - xstar‖ ^ 2 ∂P ≤ ∫ ω, ‖x k ω - xstar‖ ^ 2 ∂P
        - 2 * h k * (∫ ω, f (x k ω) ∂P - f xstar - D) + h k ^ 2 * L₀ ^ 2 * (n + 4) ^ 2 := by
    intro k hr
    refine RGF6.step_lemma P f hf L₀ hL₀ hLip xstar μ hμ (h k) (hh k).le (x k) (u k) (x (k + 1))
      (hxm k).1 (hu k) (hxm (k + 1)).1 (hxm k).2 (hrun.law_dir k) hr ?_
    intro ω
    have h1 := hrun.step k ω
    exact RGF6.proj_nonexp hQconv h1.1 h1.2 hxstar
  have hr0 : ∫ ω, ‖x 0 ω - xstar‖ ^ 2 ∂P = ‖x₀ - xstar‖ ^ 2 := by
    simp [hrun.init]
  have hr : ∀ k, Integrable (fun ω => ‖x k ω - xstar‖ ^ 2) P := by
    intro k
    induction k with
    | zero => simp [hrun.init]
    | succ k ih => exact (hgen k ih).1
  have hsum : ∀ N : ℕ, ∫ ω, ‖x (N + 1) ω - xstar‖ ^ 2 ∂P
      + 2 * ∑ k ∈ Finset.range (N + 1), h k * (∫ ω, f (x k ω) ∂P - f xstar - D)
      ≤ ‖x₀ - xstar‖ ^ 2 + L₀ ^ 2 * (n + 4) ^ 2 * ∑ k ∈ Finset.range (N + 1), h k ^ 2 := by
    intro N
    induction N with
    | zero =>
      have := (hgen 0 (hr 0)).2.2
      rw [hr0] at this
      simp only [zero_add, Finset.range_one, Finset.sum_singleton]
      nlinarith
    | succ N ih =>
      have := (hgen (N + 1) (hr (N + 1))).2.2
      rw [Finset.sum_range_succ _ (N + 1), Finset.sum_range_succ (fun k => h k ^ 2) (N + 1)]
      nlinarith
  have hS : 0 < ∑ k ∈ Finset.range (N + 1), h k :=
    Finset.sum_pos (fun k _ => hh k) ⟨0, by simp⟩
  have h1 := hsum N
  have h2 : 0 ≤ ∫ ω, ‖x (N + 1) ω - xstar‖ ^ 2 ∂P :=
    integral_nonneg (fun ω => sq_nonneg _)
  have h3 : ∑ k ∈ Finset.range (N + 1), h k * (∫ ω, f (x k ω) ∂P - f xstar - D)
      = ∑ k ∈ Finset.range (N + 1), h k * (∫ ω, f (x k ω) ∂P - f xstar)
        - D * ∑ k ∈ Finset.range (N + 1), h k := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  set S := ∑ k ∈ Finset.range (N + 1), h k with hSdef
  set A := ∑ k ∈ Finset.range (N + 1), h k * (∫ ω, f (x k ω) ∂P - f xstar) with hA
  have h4 : A ≤ S * D + (1 / 2 * ‖x₀ - xstar‖ ^ 2 + (n + 4) ^ 2 / 2 * L₀ ^ 2 *
      ∑ k ∈ Finset.range (N + 1), h k ^ 2) := by
    rw [h3] at h1
    nlinarith
  calc 1 / S * A ≤ 1 / S * (S * D + (1 / 2 * ‖x₀ - xstar‖ ^ 2 + (n + 4) ^ 2 / 2 * L₀ ^ 2 *
      ∑ k ∈ Finset.range (N + 1), h k ^ 2)) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = D + 1 / S * (1 / 2 * ‖x₀ - xstar‖ ^ 2 + (n + 4) ^ 2 / 2 * L₀ ^ 2 *
      ∑ k ∈ Finset.range (N + 1), h k ^ 2) := by
        field_simp
