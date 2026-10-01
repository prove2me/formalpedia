-- Prove2me | solution 1 for RandomGradFree.Nonsmooth.smoothing_hasGradient
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T15:57:48.151265+00:00
-- url     : https://prove2.me/submissions/69049efe-408e-4c1f-bb24-22738d721028

import Definitions.Def_RandomGradFree_Nonsmooth_oracle
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Tactic
import Definitions.Def_RandomGradFree_Shared_smoothing
import Definitions.Def_RandomGradFree_Shared_oracle
open MeasureTheory ProbabilityTheory
namespace RGF6
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


end coord
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


end Eside
end RGF6

namespace RGF6
open MeasureTheory ProbabilityTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma cm_shift_E (F : E → ℝ) (hc : Continuous F) (c : E) :
    (∫ u, F (u+c) ∂(stdGaussian E)) =
      ∫ u, F u*Real.exp (inner ℝ u c-‖c‖^2/2) ∂(stdGaussian E) := by
  have hc1 : Continuous (fun u => F (u+c)) := hc.comp (continuous_id.add continuous_const)
  have hc2 : Continuous (fun u => F u*Real.exp (inner ℝ u c-‖c‖^2/2)) := hc.mul (by fun_prop)
  rw [stdG_def,integral_map Aop_meas.aemeasurable hc1.aestronglyMeasurable,
    integral_map Aop_meas.aemeasurable hc2.aestronglyMeasurable]
  let w := fun i => inner ℝ (stdOrthonormalBasis ℝ E i) c
  have hw : Aop E w = c := Aop_repr c
  have hnorm : ∑ i, w i^2 = ‖c‖^2 := by rw [←norm_Aop_sq,hw]
  have hadd (y : Fin (Module.finrank ℝ E) → ℝ) : Aop E (y+w) = Aop E y+c := by
    unfold Aop
    simp only [Pi.add_apply,add_smul,Finset.sum_add_distrib]
    rw [show (∑ i, w i • stdOrthonormalBasis ℝ E i)=c from hw]
  have hh := cm_shift (fun y => F (Aop E y)) w
  simp only [hadd,hnorm] at hh
  convert! hh using 1
  congr 1
  ext y
  rw [inner_Aop]
  congr 2
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  dsimp [w]
  ring

lemma int_polyexp {G : E → ℝ} (hG : AEStronglyMeasurable G (stdGaussian E))
    (C a : ℝ) (m : ℕ) (hC : 0 ≤ C) (ha : 0 ≤ a)
    (hb : ∀ u, |G u| ≤ C*(1+‖u‖)^m*Real.exp (a*‖u‖)) :
    Integrable G (stdGaussian E) := by
  rw [stdG_def] at hG ⊢
  refine (integrable_map_measure hG Aop_meas.aemeasurable).mpr ?_
  refine integrable_poly (hG.comp_aemeasurable Aop_meas.aemeasurable) C a m hC ?_
  intro y
  apply (hb (Aop E y)).trans
  have hsg := sg_nonneg y
  gcongr <;> first | positivity | exact norm_Aop_le y

lemma kernel_derivative (F : E → ℝ) (u h : E) :
    HasFDerivAt (fun h : E => F u*Real.exp (inner ℝ u h-‖h‖^2/2))
      ((F u*Real.exp (inner ℝ u h-‖h‖^2/2)) • (InnerProductSpace.toDual ℝ E (u-h))) h := by
  have hh := ((innerSL ℝ u).hasFDerivAt).sub
    (((hasStrictFDerivAt_norm_sq h).hasFDerivAt).const_mul (1/2:ℝ))
  convert! hh.exp.const_mul (F u) using 1
  · ext z
    change F u * Real.exp (inner ℝ u z-‖z‖^2/2) = F u*Real.exp (inner ℝ u z-(1/2)*‖z‖^2)
    congr 2
    ring
  · ext v
    simp [InnerProductSpace.toDual_apply_apply,inner_sub_left,innerSL_apply_apply,smul_eq_mul]
    ring

lemma gaussian_shift_hasFDerivAt (F : E → ℝ) (hc : Continuous F)
    (C K : ℝ) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hb : ∀ u, |F u| ≤ C+K*‖u‖) :
    HasFDerivAt (fun h : E => ∫ u, F (u+h) ∂(stdGaussian E))
      (InnerProductSpace.toDual ℝ E (∫ u, F u • u ∂(stdGaussian E))) 0 := by
  let B := fun u : E => (C+K*‖u‖)*Real.exp ‖u‖*(‖u‖+1)
  have hBi : Integrable B (stdGaussian E) := by
    refine int_polyexp (by fun_prop) (C+K) 1 2 (by positivity) (by norm_num) ?_
    intro u
    dsimp [B]
    rw [abs_of_nonneg (by positivity)]
    have hh : C+K*‖u‖ ≤ (C+K)*(1+‖u‖) := by nlinarith [norm_nonneg u]
    calc
      _ ≤ (C+K)*(1+‖u‖)*Real.exp ‖u‖*(‖u‖+1) := by gcongr
      _ = _ := by simp only [one_mul]; ring
  have hFi : Integrable F (stdGaussian E) := by
    refine int_polyexp hc.aestronglyMeasurable (C+K) 0 1 (by positivity) (by norm_num) ?_
    intro u
    simp only [zero_mul,Real.exp_zero,mul_one,pow_one]
    exact (hb u).trans (by nlinarith [norm_nonneg u])
  have hFu : Integrable (fun u => F u • u) (stdGaussian E) := by
    have hi : Integrable (fun u : E => (C+K)*(1+‖u‖)^2) (stdGaussian E) := by
      refine int_polyexp (by fun_prop) (C+K) 0 2 (by positivity) (by norm_num) ?_
      intro u
      simp [abs_of_nonneg (show 0 ≤ (C+K)*(1+‖u‖)^2 by positivity)]
    refine Integrable.mono' hi (hc.smul continuous_id).aestronglyMeasurable ?_
    filter_upwards [] with u
    rw [norm_smul,Real.norm_eq_abs]
    have hh := mul_le_mul_of_nonneg_right (hb u) (norm_nonneg u)
    nlinarith [norm_nonneg u,sq_nonneg ‖u‖,mul_nonneg hC (sq_nonneg ‖u‖)]
  have hd := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun h u => F u*Real.exp (inner ℝ u h-‖h‖^2/2))
    (F' := fun h u => (F u*Real.exp (inner ℝ u h-‖h‖^2/2)) • (InnerProductSpace.toDual ℝ E (u-h)))
    (bound := B) (Metric.ball_mem_nhds (0:E) (by norm_num : (0:ℝ)<1))
    (Filter.Eventually.of_forall (fun h => (hc.mul (by fun_prop)).aestronglyMeasurable))
    (by simpa using hFi)
    (by fun_prop)
    (Filter.Eventually.of_forall (fun u h hh => ?_)) hBi
    (Filter.Eventually.of_forall (fun u h _ => kernel_derivative F u h))
  · have heq : (fun h : E => ∫ u, F (u+h) ∂(stdGaussian E)) =
        (fun h : E => ∫ u, F u*Real.exp (inner ℝ u h-‖h‖^2/2) ∂(stdGaussian E)) :=
      funext (cm_shift_E F hc)
    rw [heq]
    convert! hd using 1
    simp only [inner_zero_right,norm_zero,zero_pow (by norm_num : 2≠0),zero_div,sub_zero,
      Real.exp_zero,mul_one]
    convert! ((InnerProductSpace.toDual ℝ E).toContinuousLinearEquiv.integral_comp_comm
      (μ := stdGaussian E) (fun u => F u • u)).symm using 1
    congr 1
    ext u
    simp
  · have hh' : ‖h‖ < 1 := by simpa using hh
    have hexp : Real.exp (inner ℝ u h-‖h‖^2/2) ≤ Real.exp ‖u‖ := by
      apply Real.exp_le_exp.mpr
      have hin := real_inner_le_norm u h
      have hmul := mul_le_mul_of_nonneg_left hh'.le (norm_nonneg u)
      nlinarith [sq_nonneg ‖h‖]
    have hsub : ‖u-h‖ ≤ ‖u‖+1 := (norm_sub_le u h).trans (by linarith)
    rw [norm_smul,LinearIsometryEquiv.norm_map,norm_mul,Real.norm_eq_abs,Real.norm_of_nonneg (Real.exp_pos _).le]
    dsimp [B]
    calc
      _ ≤ (C+K*‖u‖)*Real.exp ‖u‖*(‖u‖+1) := by gcongr; exact hb u

end RGF6

namespace RGF6
open MeasureTheory ProbabilityTheory RandomGradFree.Shared
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma lipschitz_cont (f : E → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ x y, |f x-f y| ≤ L*‖x-y‖) : Continuous f := by
  refine (LipschitzWith.of_dist_le_mul (K := L.toNNReal) (fun x y => ?_)).continuous
  simpa only [Real.dist_eq,dist_eq_norm,Real.norm_eq_abs,Real.coe_toNNReal _ hL] using hlip x y

lemma nonsmooth_integrable (f : E → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ x y, |f x-f y| ≤ L*‖x-y‖) (μ : ℝ) (hμ : 0 ≤ μ) (x : E) :
    Integrable (fun u => f (x+μ • u) • u) (stdGaussian E) := by
  have hc := lipschitz_cont f L hL hlip
  have h1 : Integrable (fun u : E => ‖u‖) (stdGaussian E) := IsGaussian.integrable_id.norm
  have h2 : Integrable (fun u : E => ‖u‖^2) (stdGaussian E) :=
    (IsGaussian.memLp_id (stdGaussian E) (2:ℕ) (by simp)).integrable_norm_pow (by norm_num)
  refine Integrable.mono' ((h1.const_mul |f x|).add (h2.const_mul (L*μ)))
    ((hc.comp (by fun_prop)).smul continuous_id).aestronglyMeasurable ?_
  filter_upwards [] with u
  have hh := hlip (x+μ • u) x
  rw [add_sub_cancel_left,norm_smul,Real.norm_of_nonneg hμ] at hh
  have hfn : |f (x+μ • u)| ≤ |f x|+L*μ*‖u‖ := by
    have htri := abs_add_le (f (x+μ • u)-f x) (f x)
    rw [sub_add_cancel] at htri
    nlinarith
  have hm := mul_le_mul_of_nonneg_right hfn (norm_nonneg u)
  rw [norm_smul,Real.norm_eq_abs]
  dsimp only [Pi.add_apply]
  nlinarith

lemma nonsmooth_gradient (f : E → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ x y, |f x-f y| ≤ L*‖x-y‖) (μ : ℝ) (hμ : 0 < μ) (x : E) :
    HasGradientAt (smoothing f μ)
      (∫ u, RandomGradFree.Nonsmooth.oracle f μ x u ∂(stdGaussian E)) x := by
  have hc := lipschitz_cont f L hL hlip
  let F := fun u => f (x+μ • u)
  have hFc : Continuous F := hc.comp (by fun_prop)
  have hb (u : E) : |F u| ≤ |f x|+(L*μ)*‖u‖ := by
    have hh := hlip (x+μ • u) x
    rw [add_sub_cancel_left,norm_smul,Real.norm_of_nonneg hμ.le] at hh
    have ht := abs_add_le (f (x+μ • u)-f x) (f x)
    rw [sub_add_cancel] at ht
    dsimp [F]
    nlinarith
  have hbase := gaussian_shift_hasFDerivAt F hFc |f x| (L*μ) (abs_nonneg _) (by positivity) hb
  let H := fun h : E => ∫ u, F (u+h) ∂(stdGaussian E)
  have haff : HasFDerivAt (fun z : E => μ⁻¹ • (z-x)) (μ⁻¹ • ContinuousLinearMap.id ℝ E) x := by
    convert! ((hasFDerivAt_id x).sub_const x).const_smul μ⁻¹ using 1
  have hcomp : HasFDerivAt (fun z : E => H (μ⁻¹ • (z-x)))
      ((InnerProductSpace.toDual ℝ E (∫ u, F u • u ∂(stdGaussian E))).comp
        (μ⁻¹ • ContinuousLinearMap.id ℝ E)) x := by
    have hh : HasFDerivAt H (InnerProductSpace.toDual ℝ E (∫ u, F u • u ∂(stdGaussian E)))
        (μ⁻¹ • (x-x)) := by simpa using hbase
    exact hh.comp x haff
  have heq : (fun z : E => H (μ⁻¹ • (z-x))) = smoothing f μ := by
    ext z
    dsimp [H,F,smoothing]
    congr 1
    ext u
    congr 1
    rw [smul_add,smul_smul,mul_inv_cancel₀ hμ.ne',one_smul]
    abel
  have huf := nonsmooth_integrable f L hL hlip μ hμ.le x
  have horacle : (∫ u, RandomGradFree.Nonsmooth.oracle f μ x u ∂(stdGaussian E)) =
      μ⁻¹ • (∫ u, F u • u ∂(stdGaussian E)) := by
    have hid : Integrable (fun u : E => u) (stdGaussian E) := IsGaussian.integrable_id
    have hpoint (u : E) : RandomGradFree.Nonsmooth.oracle f μ x u = μ⁻¹ • (F u • u-f x • u) := by
      simp only [RandomGradFree.Nonsmooth.oracle,F,div_eq_mul_inv,smul_sub,smul_smul]
      rw [←sub_smul]
      congr 1
      ring
    simp_rw [hpoint]
    have hfu : Integrable (fun u => F u • u) (stdGaussian E) := huf
    have hconst : Integrable (fun u : E => f x • u) (stdGaussian E) := hid.smul (f x)
    rw [integral_smul,integral_sub hfu hconst,integral_smul,integral_id_stdGaussian]
    simp
  apply hasGradientAt_iff_hasFDerivAt.mpr
  rw [horacle]
  rw [heq] at hcomp
  convert! hcomp using 1
  ext u
  simp

end RGF6

namespace RandomGradFree.Nonsmooth

theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (L₀ : ℝ) (hL₀ : 0 ≤ L₀) (hLip : ∀ x y, |f x - f y| ≤ L₀ * ‖x - y‖)
    (μ : ℝ) (hμ : 0 < μ) (x : E) :
    HasGradientAt (RandomGradFree.Shared.smoothing f μ) (∫ u, oracle f μ x u ∂(stdGaussian E)) x := by
  exact RGF6.nonsmooth_gradient f L₀ hL₀ hLip μ hμ x

end RandomGradFree.Nonsmooth
