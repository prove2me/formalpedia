-- Prove2me | solution 1 for PrivateAgnosticHalfspace.Gaussian.lemma_C_2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T22:34:47.156369+00:00
-- url     : https://prove2.me/submissions/52c527b6-6181-4ff6-a8ff-3bb2b3f2caa3

import Definitions.Def_PrivateAgnosticHalfspace_Gaussian_Regression
import Definitions.Def_ChapterHermiteProductBasis
import Theorems.Thm_PrivateAgnosticHalfspace_Gaussian_lemma_B_8
import Mathlib
import Theorems.Thm_PrivateAgnosticHalfspace_Gaussian_lemma_B_9
section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace PrivateAgnosticHalfspace.Gaussian
lemma lintegral_fin_prod {n : ℕ} {Y : Fin n → Type*} [∀ i, MeasurableSpace (Y i)]
    (μ : ∀ i, Measure (Y i)) [∀ i, SigmaFinite (μ i)]
    (f : ∀ i, Y i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    (∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂μ i := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      _ = ∫⁻ x : Y 0 × ((i : Fin n) → Y i.succ),
          f 0 x.1 * ∏ i : Fin n, f i.succ (x.2 i)
          ∂(μ 0).prod (Measure.pi (fun i => μ i.succ)) := by
        rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp_emb
          (MeasurableEquiv.measurableEmbedding _) (fun x => ∏ i, f i (x i))]
        simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
          Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
          Fin.zero_succAbove, cast_eq, Fin.cons_zero]
      _ = (∫⁻ x, f 0 x ∂μ 0) * ∏ i : Fin n, ∫⁻ x, f i.succ x ∂μ i.succ := by
        have hh := lintegral_prod_mul (μ := μ 0) (ν := Measure.pi (fun i : Fin n => μ i.succ))
          (f := f 0) (g := fun x => ∏ i : Fin n, f i.succ (x i))
          (hf 0).aemeasurable
          ((Finset.measurable_prod _ (fun i _ => (hf i.succ).comp (measurable_pi_apply i))).aemeasurable)
        rw [ih _ _ (fun i => hf i.succ)] at hh
        exact hh
      _ = _ := by rw [Fin.prod_univ_succ]

lemma lintegral_fintype_prod {ι : Type*} [Fintype ι] {Y : ι → Type*} [∀ i, MeasurableSpace (Y i)]
    (μ : ∀ i, Measure (Y i)) [∀ i, SigmaFinite (μ i)]
    (f : ∀ i, Y i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    (∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂μ i := by
  let e := (Fintype.equivFin ι).symm
  rw [← (measurePreserving_piCongrLeft _ e).lintegral_comp_emb
    (MeasurableEquiv.measurableEmbedding _) (fun x => ∏ i, f i (x i))]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  exact lintegral_fin_prod _ _ (fun i => hf _)

lemma pi_withDensity {ι : Type*} [Fintype ι] {Y : ι → Type*} [∀ i, MeasurableSpace (Y i)]
    (μ : ∀ i, Measure (Y i)) [∀ i, SigmaFinite (μ i)]
    (f : ∀ i, Y i → ℝ≥0∞) (hf : ∀ i, Measurable (f i))
    (hfin : ∀ i x, f i x ≠ ∞) :
    Measure.pi (fun i => (μ i).withDensity (f i)) =
      (Measure.pi μ).withDensity (fun x => ∏ i, f i (x i)) := by
  letI (i : ι) : SigmaFinite ((μ i).withDensity (f i)) :=
    SigmaFinite.withDensity_of_ne_top' (hfin i)
  apply Measure.pi_eq
  intro s hs
  have hm : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
  rw [withDensity_apply _ hm, ← lintegral_indicator hm]
  calc
    _ = ∫⁻ x, ∏ i, (s i).indicator (f i) (x i) ∂Measure.pi μ := by
      apply lintegral_congr
      intro x
      by_cases hx : x ∈ Set.univ.pi s
      · have hx' : ∀ i, x i ∈ s i := by simpa using hx
        simp only [Set.indicator_of_mem hx]
        apply Finset.prod_congr rfl
        intro i _
        rw [Set.indicator_of_mem (hx' i)]
      · rw [Set.indicator_of_notMem hx]
        have hbad : ∃ i, x i ∉ s i := by simpa using hx
        obtain ⟨i,hi⟩ := hbad
        symm
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        exact Set.indicator_of_notMem hi _
    _ = ∏ i, ∫⁻ x, (s i).indicator (f i) x ∂μ i := lintegral_fintype_prod _ _ (fun i => (hf i).indicator (hs i))
    _ = ∏ i, (μ i).withDensity (f i) (s i) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [lintegral_indicator (hs i), withDensity_apply _ (hs i)]
end PrivateAgnosticHalfspace.Gaussian
namespace PrivateAgnosticHalfspace.Gaussian
lemma map_withDensity_equiv {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (e : X ≃ᵐ Y) (μ : Measure X) (f : X → ℝ≥0∞) (hf : Measurable f) :
    (μ.withDensity f).map e = (μ.map e).withDensity (fun y => f (e.symm y)) := by
  ext U hU
  rw [Measure.map_apply e.measurable hU, withDensity_apply _ (e.measurable hU),
    withDensity_apply _ hU, ← lintegral_indicator (e.measurable hU), ← lintegral_indicator hU]
  have hmeas : Measurable (U.indicator (fun y => f (e.symm y))) := by
    simpa only [Function.comp_def] using (hf.comp e.symm.measurable).indicator hU
  rw [lintegral_map hmeas e.measurable]
  apply lintegral_congr
  intro x
  by_cases hx : e x ∈ U <;> simp [Set.indicator, hx]
end PrivateAgnosticHalfspace.Gaussian
namespace PrivateAgnosticHalfspace.Gaussian
lemma gaussian_eq_productDensity (d : ℕ) :
    gaussian d = (volume : Measure (Vec d)).withDensity (fun x =>
      ∏ i : Fin d, gaussianPDF 0 1 (x i)) := by
  have heach : (fun _ : Fin d => gaussianReal 0 1) =
      (fun _ : Fin d => (volume : Measure ℝ).withDensity (gaussianPDF 0 1)) := by
    funext i
    exact gaussianReal_of_var_ne_zero 0 (by norm_num)
  rw [gaussian, ← map_pi_eq_stdGaussian, heach,
    pi_withDensity (fun _ : Fin d => (volume : Measure ℝ))
      (fun _ => gaussianPDF 0 1) (fun _ => measurable_gaussianPDF _ _)
      (fun _ _ => gaussianPDF_lt_top.ne)]
  let e := MeasurableEquiv.toLp 2 (Fin d → ℝ)
  have hprod : Measurable (fun x : Fin d → ℝ => ∏ i, gaussianPDF 0 1 (x i)) :=
    Finset.measurable_prod _ (fun i _ => (measurable_gaussianPDF _ _).comp (measurable_pi_apply i))
  have hh := map_withDensity_equiv e (Measure.pi (fun _ : Fin d => (volume : Measure ℝ)))
    (fun x => ∏ i, gaussianPDF 0 1 (x i)) hprod
  have hvol : (Measure.pi (fun _ : Fin d => (volume : Measure ℝ))).map e =
      (volume : Measure (Vec d)) := (PiLp.volume_preserving_toLp (Fin d)).map_eq
  rw [hvol] at hh
  exact hh
end PrivateAgnosticHalfspace.Gaussian
namespace PrivateAgnosticHalfspace.Gaussian
noncomputable def densityConstant (d : ℕ) : ℝ := (Real.sqrt (2 * Real.pi))⁻¹ ^ d
noncomputable def gaussianWeight (d : ℕ) (x : Vec d) : ℝ :=
  densityConstant d * Real.exp (-‖x‖ ^ 2 / 2)

lemma densityConstant_pos (d : ℕ) : 0 < densityConstant d := by
  unfold densityConstant
  positivity

lemma gaussianWeight_pos (d : ℕ) (x : Vec d) : 0 < gaussianWeight d x :=
  mul_pos (densityConstant_pos d) (Real.exp_pos _)

lemma continuous_gaussianWeight (d : ℕ) : Continuous (gaussianWeight d) := by
  unfold gaussianWeight
  fun_prop

lemma gaussianPDF_product (d : ℕ) (x : Vec d) :
    (∏ i : Fin d, gaussianPDF 0 1 (x i)) = ENNReal.ofReal (gaussianWeight d x) := by
  simp only [gaussianPDF]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => gaussianPDFReal_nonneg _ _ _)]
  congr 1
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← Real.exp_sum]
  unfold gaussianWeight densityConstant
  congr 2
  rw [EuclideanSpace.real_norm_sq_eq]
  rw [← Finset.sum_div, Finset.sum_neg_distrib]

lemma gaussian_eq_withDensity (d : ℕ) :
    gaussian d = (volume : Measure (Vec d)).withDensity (fun x => ENNReal.ofReal (gaussianWeight d x)) := by
  rw [gaussian_eq_productDensity]
  congr 1
  funext x
  exact gaussianPDF_product d x

lemma volume_absolutelyContinuous_gaussian (d : ℕ) :
    (volume : Measure (Vec d)) ≪ gaussian d := by
  rw [gaussian_eq_withDensity]
  exact withDensity_absolutelyContinuous' (continuous_gaussianWeight d).measurable.ennreal_ofReal.aemeasurable
    (ae_of_all _ (fun x => (ENNReal.ofReal_pos.mpr (gaussianWeight_pos d x)).ne'))

lemma gaussian_absolutelyContinuous_volume (d : ℕ) :
    gaussian d ≪ (volume : Measure (Vec d)) := by
  rw [gaussian_eq_withDensity]
  exact withDensity_absolutelyContinuous _ _
end PrivateAgnosticHalfspace.Gaussian
namespace PrivateAgnosticHalfspace.Gaussian
open BookProof.HermiteProductCore
lemma gaussianWeight_eq_gaussD (d : ℕ) (x : Vec d) :
    gaussianWeight d x = densityConstant d * (gaussD x) ^ 2 := by
  unfold gaussianWeight gaussD
  simp only [pow_two]
  rw [← Real.exp_add]
  congr 2
  ring

lemma gaussian_integrable_iff_weighted (d : ℕ) (f : Vec d → ℝ) :
    Integrable f (gaussian d) ↔ Integrable (fun x => gaussianWeight d x * f x) volume := by
  rw [gaussian_eq_withDensity]
  have hh := integrable_withDensity_iff_integrable_smul'
    (continuous_gaussianWeight d).measurable.ennreal_ofReal (by simp :
      ∀ᵐ x ∂(volume : Measure (Vec d)), ENNReal.ofReal (gaussianWeight d x) < ∞)
    (g := f)
  simpa only [ENNReal.toReal_ofReal (gaussianWeight_pos d _).le, smul_eq_mul] using hh

lemma gaussian_memLp_weighted (d : ℕ) (f : Vec d → ℝ) (hf : MemLp f 2 (gaussian d)) :
    MemLp (fun x => f x * gaussD x) 2 (volume : Measure (Vec d)) := by
  have hfm : AEStronglyMeasurable f (volume : Measure (Vec d)) :=
    hf.aestronglyMeasurable.mono_ac (volume_absolutelyContinuous_gaussian d)
  have hgm : AEStronglyMeasurable (fun x => f x * gaussD x) volume :=
    hfm.mul continuous_gaussD.aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq hgm).2
  have hI := (gaussian_integrable_iff_weighted d (fun x => f x ^ 2)).1 hf.integrable_sq
  have hJ := hI.const_mul (densityConstant d)⁻¹
  apply hJ.congr
  apply ae_of_all
  intro x
  change (densityConstant d)⁻¹ * (gaussianWeight d x * f x ^ 2) = (f x * gaussD x) ^ 2
  rw [gaussianWeight_eq_gaussD]
  have hc : densityConstant d ≠ 0 := (densityConstant_pos d).ne'
  field_simp
  <;> ring
end PrivateAgnosticHalfspace.Gaussian
namespace PrivateAgnosticHalfspace.Gaussian
open BookProof.HermiteProductCore
lemma gaussian_memLp_of_weighted (d : ℕ) (f : Vec d → ℝ)
    (hf : MemLp (fun x => f x * gaussD x) 2 (volume : Measure (Vec d))) :
    MemLp f 2 (gaussian d) := by
  have hfm : AEStronglyMeasurable f (volume : Measure (Vec d)) := by
    have hh := hf.aestronglyMeasurable.mul (continuous_gaussD.inv₀ gaussD_ne_zero).aestronglyMeasurable
    apply hh.congr
    apply ae_of_all
    intro x
    simp only [Pi.mul_apply] at *
    change f x * gaussD x * (gaussD x)⁻¹ = f x
    field_simp [gaussD_ne_zero x]
  have hgm := hfm.mono_ac (gaussian_absolutelyContinuous_volume d)
  apply (memLp_two_iff_integrable_sq hgm).2
  apply (gaussian_integrable_iff_weighted d (fun x => f x ^ 2)).2
  have hJ := hf.integrable_sq.const_mul (densityConstant d)
  apply hJ.congr
  apply ae_of_all
  intro x
  change densityConstant d * (f x * gaussD x) ^ 2 = gaussianWeight d x * f x ^ 2
  rw [gaussianWeight_eq_gaussD]
  ring
end PrivateAgnosticHalfspace.Gaussian

end
section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
local instance (d : ℕ) : IsProbabilityMeasure (gaussian d) := by unfold gaussian; infer_instance
local instance (d : ℕ) : IsGaussian (gaussian d) := by unfold gaussian; infer_instance
lemma holder_double (p : ℝ≥0∞) : ENNReal.HolderTriple (2*p) (2*p) p := by
  constructor
  rw [ENNReal.mul_inv (by left; norm_num) (by left; norm_num),← add_mul]
  have hh : (2:ℝ≥0∞)⁻¹ + 2⁻¹ = 1 := ENNReal.inv_two_add_inv_two
  rw [hh,one_mul]

lemma memLp_all_mul {Z : Type*} [MeasurableSpace Z] (μ : Measure Z) (f g : Z → ℝ)
    (hf : ∀ p : ℝ≥0∞, p ≠ ∞ → MemLp f p μ) (hg : ∀ p : ℝ≥0∞, p ≠ ∞ → MemLp g p μ) :
    ∀ p : ℝ≥0∞, p ≠ ∞ → MemLp (fun z => f z*g z) p μ := by
  intro p hp
  haveI := holder_double p
  exact (hg (2*p) (ENNReal.mul_ne_top (by norm_num) hp)).mul'
    (hf (2*p) (ENNReal.mul_ne_top (by norm_num) hp))

lemma gaussian_polynomial_memLp (d : ℕ) (Q : MvPolynomial (Fin d) ℝ) :
    ∀ p : ℝ≥0∞, p ≠ ∞ → MemLp (fun x : Vec d => MvPolynomial.eval (fun i => x i) Q) p (gaussian d) := by
  induction Q using MvPolynomial.induction_on with
  | C a => intro p hp; simpa using (memLp_const a (μ := gaussian d) (p := p))
  | add Q T hQ hT =>
    intro p hp
    convert! (hQ p hp).add (hT p hp) using 1
    ext x; simp only [map_add,Pi.add_apply]
  | mul_X Q i hQ =>
    have hcoord : ∀ p : ℝ≥0∞, p ≠ ∞ → MemLp (fun x : Vec d => x i) p (gaussian d) := by
      intro p hp
      have h := (EuclideanSpace.proj (𝕜 := ℝ) i).comp_memLp' (ProbabilityTheory.IsGaussian.memLp_id (gaussian d) p hp)
      simpa only [Function.comp_def,EuclideanSpace.coe_proj,id_eq] using h
    simpa only [map_mul,MvPolynomial.eval_X] using memLp_all_mul (gaussian d) _ _ hQ hcoord
end PrivateAgnosticHalfspace.Gaussian
namespace PrivateAgnosticHalfspace.Gaussian
noncomputable def momentHermiteR (n : ℕ) : Polynomial ℝ :=
  (Polynomial.hermite n).map (Int.castRingHom ℝ)
noncomputable def momentHermiteFactor {d : ℕ} (i : Fin d) (n : ℕ) : MvPolynomial (Fin d) ℝ :=
  ∑ k ∈ Finset.range (n+1), MvPolynomial.C ((momentHermiteR n).coeff k / Real.sqrt (n.factorial : ℝ)) *
    MvPolynomial.X i ^ k
noncomputable def momentHermiteTensor (d : ℕ) (κ : Fin d → ℕ) : MvPolynomial (Fin d) ℝ :=
  ∏ i, momentHermiteFactor i (κ i)
lemma eval_momentHermiteFactor {d : ℕ} (i : Fin d) (n : ℕ) (x : Vec d) :
    MvPolynomial.eval (fun j => x j) (momentHermiteFactor i n) = AMPLowDeg.RankOne.hermNorm n (x i) := by
  simp only [momentHermiteFactor,map_sum,map_mul,map_pow,MvPolynomial.eval_C,MvPolynomial.eval_X]
  have hh := Polynomial.eval_eq_sum_range (p := momentHermiteR n) (x i)
  have hd : (momentHermiteR n).natDegree = n := by
    rw [momentHermiteR,Polynomial.natDegree_map_eq_of_injective (Int.cast_injective (α := ℝ)),Polynomial.natDegree_hermite]
  rw [hd] at hh
  change (∑ k ∈ Finset.range (n+1), (momentHermiteR n).coeff k / Real.sqrt (n.factorial : ℝ) * (x i)^k) =
    (momentHermiteR n).eval (x i) / Real.sqrt (n.factorial : ℝ)
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div,← hh]
lemma eval_momentHermiteTensor (d : ℕ) (κ : Fin d → ℕ) (x : Vec d) :
    MvPolynomial.eval (fun j => x j) (momentHermiteTensor d κ) = hermite d κ x := by
  simp only [momentHermiteTensor,map_prod,eval_momentHermiteFactor,hermite]
noncomputable def cutoffPolynomial (d p : ℕ) : MvPolynomial (Fin d) ℝ :=
  ∑ κ : Index d p, momentHermiteTensor d (fun i => (κ.val i).val) ^ 2
lemma eval_cutoffPolynomial (d p : ℕ) (x : Vec d) :
    MvPolynomial.eval (fun i => x i) (cutoffPolynomial d p) = ‖features d p x‖ ^ 2 := by
  simp only [cutoffPolynomial,map_sum,map_pow,eval_momentHermiteTensor,EuclideanSpace.real_norm_sq_eq]
  rfl
lemma feature_norm_sq_integrable (d p : ℕ) :
    Integrable (fun x => ‖features d p x‖ ^ 2) (gaussian d) := by
  letI : IsProbabilityMeasure (gaussian d) := by unfold gaussian; infer_instance
  have h := (gaussian_polynomial_memLp d (cutoffPolynomial d p) 1 (by norm_num)).integrable (by norm_num)
  simpa only [eval_cutoffPolynomial] using h
lemma feature_norm_fourth_integrable (d p : ℕ) :
    Integrable (fun x => ‖features d p x‖ ^ 4) (gaussian d) := by
  letI : IsProbabilityMeasure (gaussian d) := by unfold gaussian; infer_instance
  have h := (gaussian_polynomial_memLp d (cutoffPolynomial d p ^ 2) 1 (by norm_num)).integrable (by norm_num)
  simpa only [map_pow,eval_cutoffPolynomial,← pow_mul,Nat.reduceMul] using h
end PrivateAgnosticHalfspace.Gaussian
namespace PrivateAgnosticHalfspace.Gaussian
lemma feature_norm_sq_mean (d p : ℕ) :
    (∫ x, ‖features d p x‖ ^ 2 ∂gaussian d) = featureDimension d p := by
  classical
  have ho := ((lemma_B_8 d).2.2.2 p).2.2
  have hi (κ : Index d p) : Integrable (fun x => hermite d (fun i => (κ.val i).val) x ^ 2) (gaussian d) := by
    simpa only [pow_two] using (ho κ κ).1
  have he (κ : Index d p) :
      (∫ x, hermite d (fun i => (κ.val i).val) x ^ 2 ∂gaussian d) = 1 := by
    simpa only [pow_two,ite_true] using (ho κ κ).2
  simp only [EuclideanSpace.real_norm_sq_eq]
  change (∫ x, ∑ κ : Index d p, hermite d (fun i => (κ.val i).val) x ^ 2 ∂gaussian d) = _
  rw [integral_finsetSum _ (fun κ _ => hi κ)]
  simp only [he,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
  exact congrArg Nat.cast (((lemma_B_8 d).2.2.2 p).2.1)
end PrivateAgnosticHalfspace.Gaussian

end
section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
lemma clipping_tail_from_fourth (d p : ℕ) (hd : 1 ≤ d)
    (α : ℝ) (hα : 0 < α ∧ α < 1) (hdim : (d : ℝ) ≥ 2*(p:ℝ)^2/α)
    (hfourth : (∫ x, ‖features d p x‖ ^ 4 ∂gaussian d) ≤
      Real.exp (2*(p:ℝ)^2/d) * (featureDimension d p : ℝ)^2) :
    (gaussian d).real {x | ‖features d p x‖ > 2*Real.sqrt (featureDimension d p)} ≤ α := by
  letI : IsProbabilityMeasure (gaussian d) := by unfold gaussian; infer_instance
  let D : ℝ := featureDimension d p
  let V : Vec d → ℝ := fun x => ‖features d p x‖ ^ 2 / D
  have hD : 0 < D := by
    change (0 : ℝ) < ((d+p).choose p : ℝ)
    exact_mod_cast Nat.choose_pos (by omega : p ≤ d+p)
  have hD0 : D ≠ 0 := hD.ne'
  have hW : (fun x : Vec d => (V x-1)^2) =
      (fun x => ‖features d p x‖ ^ 4 / D^2 - 2*(‖features d p x‖ ^ 2 / D) + 1) := by
    funext x; unfold V; ring
  have hi4 := feature_norm_fourth_integrable d p
  have hi2 := feature_norm_sq_integrable d p
  have hWi : Integrable (fun x => (V x-1)^2) (gaussian d) := by
    rw [hW]
    convert! ((hi4.div_const (D^2)).sub ((hi2.div_const D).const_mul 2)).add (integrable_const 1) using 1
  have hEW : (∫ x, (V x-1)^2 ∂gaussian d) =
      (∫ x, ‖features d p x‖ ^ 4 ∂gaussian d) / D^2 - 1 := by
    have h4' : Integrable (fun x => ‖features d p x‖^4 / D^2) (gaussian d) := hi4.div_const _
    have h2' : Integrable (fun x => 2*(‖features d p x‖^2/D)) (gaussian d) := (hi2.div_const D).const_mul 2
    have hA : Integrable (fun x => ‖features d p x‖^4/D^2-2*(‖features d p x‖^2/D)) (gaussian d) := by
      convert! h4'.sub h2' using 1
    rw [hW,integral_add hA (integrable_const 1),integral_sub h4' h2',
      integral_div,integral_const_mul,integral_div,feature_norm_sq_mean,integral_const,probReal_univ,one_smul]
    change _ = _
    simp only [show (featureDimension d p : ℝ)=D from rfl,div_self hD0]
    ring
  have hEWb : (∫ x, (V x-1)^2 ∂gaussian d) ≤ Real.exp (2*(p:ℝ)^2/d)-1 := by
    rw [hEW]
    apply sub_le_sub_right
    exact (div_le_iff₀ (sq_pos_of_pos hD)).mpr hfourth
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have ht : 2*(p:ℝ)^2/d ≤ α := by
    apply (div_le_iff₀ hd').mpr
    have hh := (div_le_iff₀ hα.1).mp hdim
    nlinarith
  have hexp : Real.exp α - 1 ≤ 2*α := by
    have hc := convexOn_exp.2 (Set.mem_univ (0:ℝ)) (Set.mem_univ (1:ℝ))
      (sub_nonneg.mpr hα.2.le) hα.1.le (by ring : (1-α)+α=1)
    simp only [smul_eq_mul,mul_zero,mul_one,zero_add,Real.exp_zero] at hc
    have hm := mul_le_mul_of_nonneg_left Real.exp_one_lt_three.le hα.1.le
    nlinarith
  have hEWα : (∫ x, (V x-1)^2 ∂gaussian d) ≤ 2*α :=
    hEWb.trans ((sub_le_sub_right (Real.exp_le_exp.mpr ht) 1).trans hexp)
  have hevent : {x : Vec d | ‖features d p x‖ > 2*Real.sqrt (featureDimension d p)} ⊆
      {x | 9 ≤ (V x-1)^2} := by
    intro x hx
    change 2*Real.sqrt (featureDimension d p : ℝ) < ‖features d p x‖ at hx
    have hs : Real.sqrt (featureDimension d p : ℝ)^2 = D := Real.sq_sqrt hD.le
    have hnorm := norm_nonneg (features d p x)
    have hs0 := Real.sqrt_nonneg (featureDimension d p : ℝ)
    have hv : 4 < V x := by
      apply (lt_div_iff₀ hD).mpr
      have hprod := mul_pos (sub_pos.mpr hx) (by linarith : 0 < ‖features d p x‖+2*Real.sqrt (featureDimension d p : ℝ))
      nlinarith
    change 9 ≤ (V x-1)^2
    nlinarith
  have hmass := measureReal_mono (μ := gaussian d) hevent
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all (gaussian d) (fun x => sq_nonneg (V x-1))) hWi 9
  linarith
end PrivateAgnosticHalfspace.Gaussian

end
section
open MeasureTheory Filter
open scoped BigOperators ENNReal NNReal Topology
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
lemma real_powerSeries_radius (a : ℕ → ℝ) (r : ℝ≥0)
    (ha : Summable (fun n => a n * (r : ℝ)^n)) :
    (r : ℝ≥0∞) ≤ (FormalMultilinearSeries.ofScalars ℝ a).radius := by
  have hab : |(r : ℝ)| = r := abs_of_nonneg r.2
  apply FormalMultilinearSeries.le_radius_of_summable_norm
  simpa only [FormalMultilinearSeries.ofScalars_norm,norm_mul,norm_pow,Real.norm_eq_abs,
    hab] using ha.norm

lemma powerSeries_unique_positive (a b : ℕ → ℝ) (r : ℝ≥0) (hr : 0 < r)
    (ha : Summable (fun n => a n * (r : ℝ)^n)) (hb : Summable (fun n => b n * (r : ℝ)^n))
    (heq : ∀ t : ℝ, 0 < t → t < r → (∑' n, a n*t^n) = ∑' n, b n*t^n) : a = b := by
  let A := FormalMultilinearSeries.ofScalars ℝ a
  let B := FormalMultilinearSeries.ofScalars ℝ b
  have hAr := real_powerSeries_radius a r ha
  have hBr := real_powerSeries_radius b r hb
  have hr' : (0 : ℝ≥0∞) < r := by exact_mod_cast hr
  have hA := A.hasFPowerSeriesOnBall (lt_of_lt_of_le hr' hAr)
  have hB := B.hasFPowerSeriesOnBall (lt_of_lt_of_le hr' hBr)
  have hfreq : ∃ᶠ t in 𝓝[≠] (0 : ℝ), A.sum t = B.sum t := by
    have hi : (0 : ℝ) ∈ closure (Set.Ioo (0:ℝ) r) := by
      rw [closure_Ioo (ne_of_lt (show (0 : ℝ) < r by exact_mod_cast hr))]
      exact ⟨le_rfl,le_of_lt (by exact_mod_cast hr)⟩
    have hset : Set.Ioo (0 : ℝ) r \ {0} = Set.Ioo (0 : ℝ) r := by
      ext t
      constructor
      · exact fun ht => ht.1
      · intro ht
        exact ⟨ht, by simp only [Set.mem_singleton_iff]; linarith [ht.1]⟩
    have hi' : (0 : ℝ) ∈ closure (Set.Ioo (0 : ℝ) r \ {0}) := by rwa [hset]
    have hf := mem_closure_ne_iff_frequently_within.mp hi' 
    apply hf.mono
    intro t ht
    change FormalMultilinearSeries.ofScalarsSum a t = FormalMultilinearSeries.ofScalarsSum b t
    simpa only [FormalMultilinearSeries.ofScalars_sum_eq,smul_eq_mul] using heq t ht.1 ht.2
  have hev := (hA.analyticAt.frequently_eq_iff_eventually_eq hB.analyticAt).mp hfreq
  apply FormalMultilinearSeries.ofScalars_series_injective ℝ ℝ
  exact hA.hasFPowerSeriesAt.eq_formalMultilinearSeries_of_eventually hB.hasFPowerSeriesAt hev
end PrivateAgnosticHalfspace.Gaussian

end
section
open MeasureTheory
open scoped BigOperators
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
lemma hasSum_integral_nonneg {ι Z : Type*} [Countable ι] [MeasurableSpace Z]
    (μ : Measure Z) (F : ι → Z → ℝ) (f : Z → ℝ)
    (hFi : ∀ i, Integrable (F i) μ) (hF0 : ∀ i z, 0 ≤ F i z)
    (hfi : Integrable f μ) (hs : ∀ z, HasSum (fun i => F i z) (f z)) :
    HasSum (fun i => ∫ z, F i z ∂μ) (∫ z, f z ∂μ) := by
  apply hasSum_integral_of_dominated_convergence F (fun i => (hFi i).1)
  · intro i
    exact ae_of_all μ (fun z => by rw [Real.norm_eq_abs,abs_of_nonneg (hF0 i z)])
  · exact ae_of_all μ (fun z => (hs z).summable)
  · simpa only [(hs _).tsum_eq] using hfi
  · exact ae_of_all μ hs
end PrivateAgnosticHalfspace.Gaussian

end
section
set_option autoImplicit false
open scoped BigOperators
lemma real_product_summable {A B : Type*} (f : A → ℝ) (g : B → ℝ)
    (hf : Summable f) (hg : Summable g) : Summable (fun p : A × B => f p.1 * g p.2) := by
  exact summable_mul_of_summable_norm hf.norm hg.norm

end
section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
lemma hasSum_fin_product {Y : Type*} {n : ℕ} (f : Fin n → Y → ℝ) (a : Fin n → ℝ)
    (hf : ∀ i, HasSum (f i) (a i)) :
    HasSum (fun y : Fin n → Y => ∏ i, f i (y i)) (∏ i, a i) := by
  induction n with
  | zero => simpa using (hasSum_fintype (fun y : Fin 0 → Y => ∏ i, f i (y i)))
  | succ n ih =>
    have htail := ih (fun i : Fin n => f i.succ) (fun i => a i.succ) (fun i => hf i.succ)
    let g : (Fin n → Y) → ℝ := fun y => ∏ i : Fin n, f i.succ (y i)
    have htail' : HasSum g (∏ i : Fin n, a i.succ) := htail
    have hs := real_product_summable (f 0) g (hf 0).summable htail'.summable
    have hh := (hf 0).mul htail' hs
    rw [← (Fin.consEquiv (fun _ : Fin (n+1) => Y)).hasSum_iff]
    simpa only [g,Function.comp_def,Fin.consEquiv_apply,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ] using hh
end PrivateAgnosticHalfspace.Gaussian

end
section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
noncomputable def cutoffIndexEquiv (d p : ℕ) :
    Index d p ≃ {κ : Fin d → ℕ // ∑ i, κ i ≤ p} where
  toFun κ := ⟨fun i => (κ.val i).val, κ.property⟩
  invFun κ := ⟨fun i => ⟨κ.val i, by
    have hi : κ.val i ≤ ∑ j, κ.val j :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    omega⟩, κ.property⟩
  left_inv κ := by
    apply Subtype.ext
    funext i
    apply Fin.ext
    rfl
  right_inv κ := by
    apply Subtype.ext
    funext i
    rfl

noncomputable def gradedNaturalEquiv (d : ℕ) :
    (Σ p : ℕ, {κ : Fin d → ℕ // degree κ ≤ p}) ≃ (Fin d → ℕ) × ℕ where
  toFun q := (q.2.val,q.1-degree q.2.val)
  invFun q := ⟨degree q.1+q.2,⟨q.1,by omega⟩⟩
  left_inv q := by
    rcases q with ⟨p,κ,hκ⟩
    have hp := Nat.add_sub_of_le hκ
    apply Sigma.ext hp
    apply (Subtype.heq_iff_coe_eq (fun ξ => by dsimp only; rw [hp])).mpr
    rfl
  right_inv q := by
    rcases q with ⟨κ,k⟩
    simp

noncomputable def gradedIndexEquiv (d : ℕ) :
    (Σ p : ℕ, Index d p) ≃ (Fin d → ℕ) × ℕ :=
  (Equiv.sigmaCongrRight (fun p => cutoffIndexEquiv d p)).trans (gradedNaturalEquiv d)

lemma gradedIndexEquiv_apply (d : ℕ) (q : Σ p : ℕ, Index d p) :
    gradedIndexEquiv d q = (fun i => (q.2.val i).val,q.1-degree (fun i => (q.2.val i).val)) := rfl

lemma cutoff_series (d : ℕ) (x : Vec d) (z : ℝ) (hz : -1 < z ∧ z < 1) :
    HasSum (fun p : ℕ => z^p * ‖features d p x‖ ^ 2)
      (((1-z^2)^(-(d:ℝ)/2) *
        Real.exp ((2*z*inner ℝ x x-z^2*(‖x‖^2+‖x‖^2))/(2*(1-z^2)))) * (1-z)⁻¹) := by
  have hm := lemma_B_9 d x x z hz
  have hg : HasSum (fun k : ℕ => z^k) (1-z)⁻¹ := hasSum_geometric_of_norm_lt_one
    (by simpa only [Real.norm_eq_abs,abs_lt] using hz)
  have hs := real_product_summable _ _ hm.summable hg.summable
  have hh := hm.mul hg hs
  have he := (gradedIndexEquiv d).hasSum_iff.mpr hh
  have hpoint (q : Σ p : ℕ, Index d p) :
      ((fun q : (Fin d → ℕ) × ℕ =>
        (z^degree q.1 * hermite d q.1 x * hermite d q.1 x) * z^q.2) ∘ gradedIndexEquiv d) q =
      z^q.1 * hermite d (fun i => (q.2.val i).val) x ^ 2 := by
    simp only [Function.comp_apply,gradedIndexEquiv_apply]
    rw [show z^degree (fun i => (q.2.val i).val) *
      hermite d (fun i => (q.2.val i).val) x * hermite d (fun i => (q.2.val i).val) x *
      z^(q.1-degree (fun i => (q.2.val i).val)) =
      (z^degree (fun i => (q.2.val i).val) * z^(q.1-degree (fun i => (q.2.val i).val))) *
      hermite d (fun i => (q.2.val i).val) x ^ 2 by ring]
    have hdeg : degree (fun i => (q.2.val i).val) ≤ q.1 := q.2.property
    rw [←pow_add,Nat.add_sub_of_le hdeg]
  have he' : HasSum (fun q : Σ p : ℕ, Index d p =>
      z^q.1 * hermite d (fun i => (q.2.val i).val) x ^ 2)
      (((1-z^2)^(-(d:ℝ)/2) *
        Real.exp ((2*z*inner ℝ x x-z^2*(‖x‖^2+‖x‖^2))/(2*(1-z^2)))) * (1-z)⁻¹) := by
    convert! he using 1
    funext q
    exact (hpoint q).symm
  have hfiber (p : ℕ) : HasSum (fun κ : Index d p => z^p * hermite d (fun i => (κ.val i).val) x ^ 2)
      (z^p * ‖features d p x‖ ^ 2) := by
    convert! hasSum_fintype (fun κ : Index d p => z^p * hermite d (fun i => (κ.val i).val) x ^ 2) using 1
    rw [← Finset.mul_sum,EuclideanSpace.real_norm_sq_eq]
    rfl
  exact he'.sigma hfiber
end PrivateAgnosticHalfspace.Gaussian

end
section
open MeasureTheory ProbabilityTheory GaussianFourier
open scoped BigOperators ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
lemma gaussian_square_mgf_aux (d : ℕ) (t : ℝ) (ht : t < 1/2) :
    Integrable (fun x : Vec d => Real.exp (t*‖x‖^2)) (gaussian d) ∧
      (∫ x : Vec d, Real.exp (t*‖x‖^2) ∂gaussian d) =
        densityConstant d * (Real.pi/(1/2-t)) ^ ((d:ℝ)/2) := by
  have hb : 0 < 1/2-t := by linarith
  have hprod (x : Vec d) : gaussianWeight d x * Real.exp (t*‖x‖^2) =
      densityConstant d * Real.exp (-(1/2-t)*‖x‖^2) := by
    unfold gaussianWeight
    rw [mul_assoc,←Real.exp_add]
    congr 2; ring
  have hi : Integrable (fun x : Vec d => Real.exp (-(1/2-t)*‖x‖^2)) volume := by
    have h := (integrable_cexp_neg_mul_sq_norm_add
      (b := ((1/2-t : ℝ) : ℂ)) (by simpa using hb) (0:ℂ) (0:Vec d)).re
    convert! h using 1
    funext x
    change Real.exp (-(1/2-t)*‖x‖^2) =
      (Complex.exp (-((1/2-t:ℝ):ℂ)*(‖x‖:ℂ)^2+(0:ℂ)*(inner ℝ (0:Vec d) x))).re
    rw [zero_mul,add_zero,←Complex.ofReal_pow,←Complex.ofReal_neg,←Complex.ofReal_mul,
      ←Complex.ofReal_exp,Complex.ofReal_re]
  have hi' : Integrable (fun x => gaussianWeight d x * Real.exp (t*‖x‖^2)) volume := by
    simpa only [hprod] using hi.const_mul (densityConstant d)
  refine ⟨(gaussian_integrable_iff_weighted d _).mpr hi',?_⟩
  rw [gaussian_eq_withDensity,integral_withDensity_eq_integral_toReal_smul
    (continuous_gaussianWeight d).measurable.ennreal_ofReal (by filter_upwards; simp)]
  simp_rw [ENNReal.toReal_ofReal (gaussianWeight_pos d _).le,smul_eq_mul,hprod]
  rw [integral_const_mul,integral_rexp_neg_mul_sq_norm hb]
  simp only [finrank_euclideanSpace_fin]

lemma gaussian_square_mgf (d : ℕ) (t : ℝ) (ht : t < 1/2) :
    Integrable (fun x : Vec d => Real.exp (t*‖x‖^2)) (gaussian d) ∧
      (∫ x : Vec d, Real.exp (t*‖x‖^2) ∂gaussian d) = (1-2*t)^(-(d:ℝ)/2) := by
  letI : IsProbabilityMeasure (gaussian d) := by unfold gaussian; infer_instance
  have hh := gaussian_square_mgf_aux d t ht
  have h0 := (gaussian_square_mgf_aux d 0 (by norm_num)).2
  simp only [zero_mul,Real.exp_zero,integral_const,probReal_univ,one_smul,sub_zero] at h0
  refine ⟨hh.1,hh.2.trans ?_⟩
  have hp : 0 < 1-2*t := by linarith
  have hq : Real.pi/(1/2-t) = (Real.pi/(1/2))/(1-2*t) := by
    have hb : 1/2-t ≠ 0 := ne_of_gt (by linarith : 0 < 1/2-t)
    field_simp
  rw [hq,Real.div_rpow (by positivity) hp.le,←mul_div_assoc,←h0]
  rw [neg_div,Real.rpow_neg hp.le]
  simp only [one_div]
end PrivateAgnosticHalfspace.Gaussian

end
section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
noncomputable def cutoffKernel (d : ℕ) (z : ℝ) (x : Vec d) : ℝ :=
  (1-z)⁻¹ * (1-z^2)^(-(d:ℝ)/2) * Real.exp (z/(1+z)*‖x‖^2)

lemma cutoff_series_clean (d : ℕ) (x : Vec d) (z : ℝ) (hz : -1 < z ∧ z < 1) :
    HasSum (fun p : ℕ => z^p * ‖features d p x‖ ^ 2) (cutoffKernel d z x) := by
  have h := cutoff_series d x z hz
  have hq : 1-z^2 ≠ 0 := by nlinarith [hz.1,hz.2]
  have hp : 1+z ≠ 0 := by linarith [hz.1]
  have he : (2*z*inner ℝ x x-z^2*(‖x‖^2+‖x‖^2))/(2*(1-z^2)) = z/(1+z)*‖x‖^2 := by
    rw [real_inner_self_eq_norm_sq]
    field_simp
    ring
  rw [he] at h
  convert! h using 1
  unfold cutoffKernel
  ring

lemma cutoff_product_integrable (d p q : ℕ) :
    Integrable (fun x => ‖features d p x‖ ^ 2 * ‖features d q x‖ ^ 2) (gaussian d) := by
  letI : IsProbabilityMeasure (gaussian d) := by unfold gaussian; infer_instance
  have h := (gaussian_polynomial_memLp d (cutoffPolynomial d p * cutoffPolynomial d q) 1 (by norm_num)).integrable (by norm_num)
  simpa only [map_mul,eval_cutoffPolynomial] using h

lemma cutoffKernel_product_integrable (d : ℕ) (z w : ℝ)
    (hz : 0 < z ∧ z < 1/16) (hw : 0 < w ∧ w < 1/16) :
    Integrable (fun x => cutoffKernel d z x * cutoffKernel d w x) (gaussian d) ∧
    (∫ x, cutoffKernel d z x * cutoffKernel d w x ∂gaussian d) =
      ((1-z)⁻¹*(1-z^2)^(-(d:ℝ)/2)) * ((1-w)⁻¹*(1-w^2)^(-(d:ℝ)/2)) *
        (1-2*(z/(1+z)+w/(1+w)))^(-(d:ℝ)/2) := by
  have hzw : z/(1+z)+w/(1+w) < 1/2 := by
    have hz' : z/(1+z) ≤ z := div_le_self hz.1.le (by linarith)
    have hw' : w/(1+w) ≤ w := div_le_self hw.1.le (by linarith)
    linarith [hz.2,hw.2]
  have hm := gaussian_square_mgf d _ hzw
  have he : (fun x => cutoffKernel d z x * cutoffKernel d w x) =
      (fun x => (((1-z)⁻¹*(1-z^2)^(-(d:ℝ)/2)) * ((1-w)⁻¹*(1-w^2)^(-(d:ℝ)/2))) *
        Real.exp ((z/(1+z)+w/(1+w))*‖x‖^2)) := by
    funext x
    unfold cutoffKernel
    rw [add_mul,Real.exp_add]
    ring
  rw [he]
  refine ⟨hm.1.const_mul _,?_⟩
  rw [integral_const_mul,hm.2]

lemma cutoff_moment_generating (d : ℕ) (z w : ℝ)
    (hz : 0 < z ∧ z < 1/16) (hw : 0 < w ∧ w < 1/16) :
    HasSum (fun pq : ℕ × ℕ => z^pq.1 * w^pq.2 *
      (∫ x, ‖features d pq.1 x‖^2 * ‖features d pq.2 x‖^2 ∂gaussian d))
      (((1-z)⁻¹*(1-z^2)^(-(d:ℝ)/2)) * ((1-w)⁻¹*(1-w^2)^(-(d:ℝ)/2)) *
        (1-2*(z/(1+z)+w/(1+w)))^(-(d:ℝ)/2)) := by
  let F : (ℕ × ℕ) → Vec d → ℝ := fun pq x =>
    z^pq.1 * w^pq.2 * (‖features d pq.1 x‖^2 * ‖features d pq.2 x‖^2)
  have hFi (pq : ℕ × ℕ) : Integrable (F pq) (gaussian d) :=
    (cutoff_product_integrable d pq.1 pq.2).const_mul _
  have hF0 : ∀ pq x, 0 ≤ F pq x := by
    intro pq x
    exact mul_nonneg (mul_nonneg (pow_nonneg hz.1.le _) (pow_nonneg hw.1.le _))
      (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hs (x : Vec d) : HasSum (fun pq => F pq x) (cutoffKernel d z x * cutoffKernel d w x) := by
    let f : ℕ → ℝ := fun p => z^p * ‖features d p x‖^2
    let g : ℕ → ℝ := fun p => w^p * ‖features d p x‖^2
    have hf : HasSum f (cutoffKernel d z x) := cutoff_series_clean d x z ⟨by linarith [hz.1],by linarith [hz.2]⟩
    have hg : HasSum g (cutoffKernel d w x) := cutoff_series_clean d x w ⟨by linarith [hw.1],by linarith [hw.2]⟩
    have hmul := hf.mul hg (real_product_summable f g hf.summable hg.summable)
    convert! hmul using 1
    funext pq; unfold F f g; ring
  have hi := cutoffKernel_product_integrable d z w hz hw
  have hh := hasSum_integral_nonneg (gaussian d) F _ hFi hF0 hi.1 hs
  rw [hi.2] at hh
  convert! hh using 1
  funext pq
  exact (integral_const_mul _ _).symm
end PrivateAgnosticHalfspace.Gaussian

end
section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
lemma cutoff_moment_generating_closed (d : ℕ) (z w : ℝ)
    (hz : 0 < z ∧ z < 1/16) (hw : 0 < w ∧ w < 1/16) :
    HasSum (fun pq : ℕ × ℕ => z^pq.1 * w^pq.2 *
      (∫ x, ‖features d pq.1 x‖^2 * ‖features d pq.2 x‖^2 ∂gaussian d))
      ((1-z)^(-(d:ℝ)-1) * (1-w)^(-(d:ℝ)-1) *
        (1-4*z*w/((1-z)*(1-w)))^(-(d:ℝ)/2)) := by
  have h := cutoff_moment_generating d z w hz hw
  have ha : 0 < 1-z := by linarith [hz.2]
  have hb : 0 < 1-w := by linarith [hw.2]
  have hP : 0 < 1-z^2 := by nlinarith [hz.1,hz.2]
  have hS : 0 < 1-w^2 := by nlinarith [hw.1,hw.2]
  have hzp : 1+z ≠ 0 := by linarith [hz.1]
  have hwp : 1+w ≠ 0 := by linarith [hw.1]
  have hQ : 0 < 1-2*(z/(1+z)+w/(1+w)) := by
    have hz' := div_le_self hz.1.le (by linarith : 1 ≤ 1+z)
    have hw' := div_le_self hw.1.le (by linarith : 1 ≤ 1+w)
    linarith [hz.2,hw.2]
  have hdet : (1-z^2)*(1-w^2)*(1-2*(z/(1+z)+w/(1+w))) =
      (1-z)^2*(1-w)^2*(1-4*z*w/((1-z)*(1-w))) := by
    field_simp
    ring
  have hc : 0 < 1-4*z*w/((1-z)*(1-w)) := by
    have hp := mul_pos (mul_pos hP hS) hQ
    rw [hdet] at hp
    exact (mul_pos_iff_of_pos_left (mul_pos (sq_pos_of_pos ha) (sq_pos_of_pos hb))).mp hp
  have hlog := congrArg Real.log hdet
  rw [Real.log_mul (mul_ne_zero hP.ne' hS.ne') hQ.ne',Real.log_mul hP.ne' hS.ne',
    Real.log_mul (mul_ne_zero (pow_ne_zero 2 ha.ne') (pow_ne_zero 2 hb.ne')) hc.ne',
    Real.log_mul (pow_ne_zero 2 ha.ne') (pow_ne_zero 2 hb.ne'),Real.log_pow,Real.log_pow] at hlog
  have hinva : (1-z)⁻¹ = Real.exp (-Real.log (1-z)) := by rw [Real.exp_neg,Real.exp_log ha]
  have hinvb : (1-w)⁻¹ = Real.exp (-Real.log (1-w)) := by rw [Real.exp_neg,Real.exp_log hb]
  have he : ((1-z)⁻¹*(1-z^2)^(-(d:ℝ)/2)) * ((1-w)⁻¹*(1-w^2)^(-(d:ℝ)/2)) *
        (1-2*(z/(1+z)+w/(1+w)))^(-(d:ℝ)/2) =
      (1-z)^(-(d:ℝ)-1) * (1-w)^(-(d:ℝ)-1) *
        (1-4*z*w/((1-z)*(1-w)))^(-(d:ℝ)/2) := by
    rw [hinva,hinvb]
    simp_rw [Real.rpow_def_of_pos hP,Real.rpow_def_of_pos hS,Real.rpow_def_of_pos hQ,
      Real.rpow_def_of_pos ha,Real.rpow_def_of_pos hb,Real.rpow_def_of_pos hc,←Real.exp_add]
    congr 1
    linear_combination (-(d:ℝ)/2)*hlog
  rwa [he] at h
end PrivateAgnosticHalfspace.Gaussian

end
section
open Filter
open scoped BigOperators ENNReal NNReal Topology
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
noncomputable def shiftedChoose (d k p : ℕ) : ℝ :=
  if k ≤ p then ((d+p).choose (p-k) : ℝ) else 0

lemma shifted_choose_series (d k : ℕ) (z : ℝ) (hz : |z| < 1) :
    HasSum (fun p : ℕ => shiftedChoose d k p * z^p)
      (z^k / (1-z)^(d+k+1)) := by
  have h := (hasSum_choose_mul_geometric_of_norm_lt_one (d+k)
    (show ‖z‖ < 1 by simpa only [Real.norm_eq_abs] using hz)).mul_left (z^k)
  have hc (n : ℕ) : shiftedChoose d k (n+k) * z^(n+k) =
      z^k * (((n+(d+k)).choose (d+k) : ℝ) * z^n) := by
    unfold shiftedChoose
    rw [if_pos (by omega),Nat.add_sub_cancel_right,pow_add]
    have he : d+(n+k)=n+(d+k) := by omega
    rw [he,Nat.choose_symm_add]
    ring
  have hsum : (∑ p ∈ Finset.range k, shiftedChoose d k p * z^p) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    have hpk : ¬ k ≤ p := by have hp' : p < k := Finset.mem_range.mp hp; omega
    simp only [shiftedChoose,if_neg hpk,zero_mul]
  have htail : HasSum (fun n => shiftedChoose d k (n+k) * z^(n+k))
      (z^k / (1-z)^(d+k+1)) := by
    convert! h using 1
    · funext n; exact hc n
    · ring
  have hall := (hasSum_nat_add_iff (f := fun p => shiftedChoose d k p * z^p) k).mp htail
  simpa only [hsum,add_zero] using hall

lemma multichoose_series (a z : ℝ) (hz : |z| < 1) :
    HasSum (fun k : ℕ => Ring.multichoose a k * z^k) (1/(1-z)^a) := by
  have hh := (Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero a).hasSum
    (show z ∈ Metric.eball (0:ℝ) 1 by simpa [Metric.mem_eball,Real.enorm_eq_ofReal_abs] using hz)
  simpa only [zero_add,FormalMultilinearSeries.ofScalars_apply_eq,smul_eq_mul,← Ring.multichoose_eq] using hh
end PrivateAgnosticHalfspace.Gaussian

end
section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
lemma hasSum_nonneg_rows {I J : Type*} (F : I → J → ℝ) (g : I → ℝ) (s : ℝ)
    (h0 : ∀ i j, 0 ≤ F i j) (hr : ∀ i, HasSum (F i) (g i)) (hg : HasSum g s) :
    HasSum (fun p : I × J => F p.1 p.2) s := by
  have hs : Summable (fun p : I × J => F p.1 p.2) := by
    apply (summable_prod_of_nonneg (fun p => h0 p.1 p.2)).mpr
    exact ⟨fun i => (hr i).summable,by simpa only [(hr _).tsum_eq] using hg.summable⟩
  have he := hs.hasSum.prod_fiberwise hr
  exact (he.unique hg) ▸ hs.hasSum

lemma multichoose_eq_product (a : ℝ) (k : ℕ) :
    Ring.multichoose a k = (∏ j ∈ Finset.range k, (a+j)) / k.factorial := by
  have hp : (ascPochhammer ℝ k).eval a = ∏ j ∈ Finset.range k, (a+j) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [ascPochhammer_succ_right,Polynomial.eval_mul,ih,Finset.prod_range_succ]
      simp
  have h := Ring.factorial_nsmul_multichoose_eq_ascPochhammer a k
  rw [nsmul_eq_mul,Polynomial.ascPochhammer_smeval_eq_eval,hp] at h
  apply (eq_div_iff (by positivity : (k.factorial : ℝ) ≠ 0)).mpr
  linarith

lemma multichoose_nonneg_real (a : ℝ) (ha : 0 ≤ a) (k : ℕ) : 0 ≤ Ring.multichoose a k := by
  rw [multichoose_eq_product]
  exact div_nonneg (Finset.prod_nonneg (fun j _ => by positivity)) (Nat.cast_nonneg _)

noncomputable def cutoffCandidate (d p q : ℕ) : ℝ :=
  ∑' k : ℕ, (4:ℝ)^k * Ring.multichoose ((d:ℝ)/2) k * shiftedChoose d k p * shiftedChoose d k q

lemma shiftedChoose_nonneg (d k p : ℕ) : 0 ≤ shiftedChoose d k p := by
  unfold shiftedChoose
  split_ifs <;> positivity
end PrivateAgnosticHalfspace.Gaussian

namespace PrivateAgnosticHalfspace.Gaussian
lemma cutoff_cross_parameter (z w : ℝ) (hz : 0 < z ∧ z < 1/16) (hw : 0 < w ∧ w < 1/16) :
    0 ≤ 4*z*w/((1-z)*(1-w)) ∧ 4*z*w/((1-z)*(1-w)) < 1 := by
  have ha : 0 < 1-z := by linarith [hz.2]
  have hb : 0 < 1-w := by linarith [hw.2]
  constructor
  · exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hz.1.le) hw.1.le) (mul_nonneg ha.le hb.le)
  · apply (div_lt_iff₀ (mul_pos ha hb)).mpr
    have hzw : z*w < z := by nlinarith [mul_pos hz.1 (by linarith [hw.2] : 0 < 1-w)]
    nlinarith [hz.2,hw.2]

lemma cutoff_candidate_generating (d : ℕ) (z w : ℝ)
    (hz : 0 < z ∧ z < 1/16) (hw : 0 < w ∧ w < 1/16) :
    HasSum (fun pq : ℕ × ℕ => z^pq.1*w^pq.2*cutoffCandidate d pq.1 pq.2)
      ((1/(1-z)^(d+1))*(1/(1-w)^(d+1)) /
        (1-4*z*w/((1-z)*(1-w)))^((d:ℝ)/2)) := by
  let u := 4*z*w/((1-z)*(1-w))
  let C := (1/(1-z)^(d+1))*(1/(1-w)^(d+1))
  let c : ℕ → ℝ := fun k => (4:ℝ)^k * Ring.multichoose ((d:ℝ)/2) k
  let f : ℕ → ℕ → ℝ := fun k p => shiftedChoose d k p * z^p
  let g : ℕ → ℕ → ℝ := fun k p => shiftedChoose d k p * w^p
  let F : ℕ → (ℕ × ℕ) → ℝ := fun k pq => c k * f k pq.1 * g k pq.2
  let A : ℕ → ℝ := fun k => c k * (z^k/(1-z)^(d+k+1)) * (w^k/(1-w)^(d+k+1))
  have ha : 0 < 1-z := by linarith [hz.2]
  have hb : 0 < 1-w := by linarith [hw.2]
  have hzn : |z| < 1 := by rw [abs_of_pos hz.1]; linarith [hz.2]
  have hwn : |w| < 1 := by rw [abs_of_pos hw.1]; linarith [hw.2]
  have hu := cutoff_cross_parameter z w hz hw
  have hrows (k : ℕ) : HasSum (F k) (A k) := by
    have hfk : HasSum (f k) (z^k/(1-z)^(d+k+1)) := shifted_choose_series d k z hzn
    have hgk : HasSum (g k) (w^k/(1-w)^(d+k+1)) := shifted_choose_series d k w hwn
    have hp := (hfk.mul hgk (real_product_summable (f k) (g k) hfk.summable hgk.summable)).mul_left (c k)
    convert! hp using 1
    · funext pq; unfold F; ring
    · unfold A; ring
  have hAeq (k : ℕ) : A k = C * (Ring.multichoose ((d:ℝ)/2) k * u^k) := by
    dsimp only [A,C,c,u]
    rw [show d+k+1=d+1+k by omega]
    simp only [pow_add,mul_pow,div_pow]
    field_simp
  have houter : HasSum A (C/(1-u)^((d:ℝ)/2)) := by
    have hp := (multichoose_series ((d:ℝ)/2) u (by rw [abs_of_nonneg hu.1]; exact hu.2)).mul_left C
    convert! hp using 1
    · funext k; exact hAeq k
    · ring
  have h0 : ∀ k pq, 0 ≤ F k pq := by
    intro k pq
    unfold F c f g
    exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity)
      (multichoose_nonneg_real _ (by positivity) _))
      (mul_nonneg (shiftedChoose_nonneg _ _ _) (pow_nonneg hz.1.le _)))
      (mul_nonneg (shiftedChoose_nonneg _ _ _) (pow_nonneg hw.1.le _))
  have hfull := hasSum_nonneg_rows F A _ h0 hrows houter
  have hswap := (Equiv.prodComm (ℕ × ℕ) ℕ).hasSum_iff.mpr hfull
  have hfiber (pq : ℕ × ℕ) : HasSum (fun k => F k pq)
      (z^pq.1*w^pq.2*cutoffCandidate d pq.1 pq.2) := by
    have hs := (hswap.summable.prod_factor pq).hasSum
    convert! hs using 1
    unfold cutoffCandidate
    rw [←tsum_mul_left]
    apply tsum_congr
    intro k
    dsimp only [Function.comp_apply,Equiv.prodComm_apply,Prod.swap]
    unfold F c f g
    ring
  exact hswap.prod_fiberwise hfiber
end PrivateAgnosticHalfspace.Gaussian

end
section
open Filter
open scoped BigOperators ENNReal NNReal Topology
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
lemma matrix_series_marginal (a : ℕ → ℕ → ℝ) (z w s : ℝ)
    (h : HasSum (fun pq : ℕ × ℕ => z^pq.1*w^pq.2*a pq.1 pq.2) s) :
    HasSum (fun p => (∑' q, a p q*w^q)*z^p) s := by
  apply h.prod_fiberwise
  intro p
  have hs := (h.summable.prod_factor p).hasSum
  convert! hs using 1
  rw [←tsum_mul_right]
  apply tsum_congr
  intro q
  ring

lemma matrix_powerSeries_unique (a b : ℕ → ℕ → ℝ) (r : ℝ≥0) (hr : 0 < r)
    (F : ℝ → ℝ → ℝ)
    (ha : ∀ z w : ℝ, 0 < z → z ≤ r → 0 < w → w ≤ r →
      HasSum (fun pq : ℕ × ℕ => z^pq.1*w^pq.2*a pq.1 pq.2) (F z w))
    (hb : ∀ z w : ℝ, 0 < z → z ≤ r → 0 < w → w ≤ r →
      HasSum (fun pq : ℕ × ℕ => z^pq.1*w^pq.2*b pq.1 pq.2) (F z w)) : a = b := by
  have hr' : (0:ℝ) < r := by exact_mod_cast hr
  have hrows (w : ℝ) (hw : 0 < w) (hwr : w ≤ r) :
      (fun p => ∑' q, a p q*w^q) = (fun p => ∑' q, b p q*w^q) := by
    apply powerSeries_unique_positive _ _ r hr
    · exact (matrix_series_marginal a r w _ (ha r w hr' le_rfl hw hwr)).summable
    · exact (matrix_series_marginal b r w _ (hb r w hr' le_rfl hw hwr)).summable
    · intro z hz hzr
      exact (matrix_series_marginal a z w _ (ha z w hz hzr.le hw hwr)).tsum_eq.trans
        (matrix_series_marginal b z w _ (hb z w hz hzr.le hw hwr)).tsum_eq.symm
  funext p
  have hA := (ha r r hr' le_rfl hr' le_rfl).summable.prod_factor p
  have hB := (hb r r hr' le_rfl hr' le_rfl).summable.prod_factor p
  have hA' : Summable (fun q => a p q*(r:ℝ)^q) := by
    apply (summable_mul_left_iff (pow_ne_zero p hr'.ne')).mp
    convert! hA using 1
    funext q; ring
  have hB' : Summable (fun q => b p q*(r:ℝ)^q) := by
    apply (summable_mul_left_iff (pow_ne_zero p hr'.ne')).mp
    convert! hB using 1
    funext q; ring
  apply powerSeries_unique_positive _ _ r hr hA' hB'
  intro w hw hwr
  exact congrFun (hrows w hw hwr.le) p
end PrivateAgnosticHalfspace.Gaussian

end
section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
lemma cutoff_moment_generating_natural (d : ℕ) (z w : ℝ)
    (hz : 0 < z ∧ z < 1/16) (hw : 0 < w ∧ w < 1/16) :
    HasSum (fun pq : ℕ × ℕ => z^pq.1 * w^pq.2 *
      (∫ x, ‖features d pq.1 x‖^2 * ‖features d pq.2 x‖^2 ∂gaussian d))
      ((1/(1-z)^(d+1))*(1/(1-w)^(d+1)) /
        (1-4*z*w/((1-z)*(1-w)))^((d:ℝ)/2)) := by
  have h := cutoff_moment_generating_closed d z w hz hw
  have ha : 0 < 1-z := by linarith [hz.2]
  have hb : 0 < 1-w := by linarith [hw.2]
  have hc : 0 < 1-4*z*w/((1-z)*(1-w)) := by have hh := cutoff_cross_parameter z w hz hw; linarith [hh.2]
  have hp (x : ℝ) (hx : 0 < x) : x^(-(d:ℝ)-1) = 1/x^(d+1) := by
    rw [show -(d:ℝ)-1 = -((d+1:ℕ):ℝ) by push_cast; ring,Real.rpow_neg hx.le,Real.rpow_natCast]
    simp only [one_div]
  rw [hp _ ha,hp _ hb,neg_div,Real.rpow_neg hc.le] at h
  simpa only [div_eq_mul_inv] using h

lemma cutoff_second_moment_formula (d p q : ℕ) :
    (∫ x, ‖features d p x‖^2 * ‖features d q x‖^2 ∂gaussian d) = cutoffCandidate d p q := by
  let a : ℕ → ℕ → ℝ := fun p q => ∫ x, ‖features d p x‖^2 * ‖features d q x‖^2 ∂gaussian d
  let b : ℕ → ℕ → ℝ := cutoffCandidate d
  let r : ℝ≥0 := ⟨1/32,by norm_num⟩
  let F : ℝ → ℝ → ℝ := fun z w => (1/(1-z)^(d+1))*(1/(1-w)^(d+1)) /
        (1-4*z*w/((1-z)*(1-w)))^((d:ℝ)/2)
  have hrpos : 0 < r := by change (0 : ℝ) < 1/32; norm_num
  have hrco : (r : ℝ) = 1/32 := rfl
  have heq : a = b := by
    apply matrix_powerSeries_unique a b r hrpos F
    · intro z w hz hzr hw hwr
      exact cutoff_moment_generating_natural d z w ⟨hz,by rw [hrco] at hzr; linarith⟩
        ⟨hw,by rw [hrco] at hwr; linarith⟩
    · intro z w hz hzr hw hwr
      exact cutoff_candidate_generating d z w ⟨hz,by rw [hrco] at hzr; linarith⟩
        ⟨hw,by rw [hrco] at hwr; linarith⟩
  exact congrFun (congrFun heq p) q
end PrivateAgnosticHalfspace.Gaussian

end
section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
lemma cutoffChoose_step (d p k : ℕ) (hk : k < p) :
    ((d+p).choose (p-(k+1)) : ℝ) =
      ((d+p).choose (p-k) : ℝ) * (p-k) / (d+k+1) := by
  have hm : p-(k+1)+1=p-k := by omega
  have hd : d+p-(p-(k+1))=d+k+1 := by omega
  have hh := Nat.choose_succ_right_eq (d+p) (p-(k+1))
  rw [hm,hd] at hh
  have hh' : ((d+p).choose (p-k) : ℝ)*(p-k) =
      ((d+p).choose (p-(k+1)) : ℝ)*(d+k+1) := by
    have hc : ((d+p).choose (p-k) : ℝ)*((p-k : ℕ) : ℝ) =
        ((d+p).choose (p-(k+1)) : ℝ)*((d+k+1 : ℕ) : ℝ) := by exact_mod_cast hh
    simpa only [Nat.cast_sub hk.le,Nat.cast_add,Nat.cast_one] using hc
  apply (eq_div_iff (by positivity : (d+k+1:ℝ) ≠ 0)).mpr
  exact hh'.symm

lemma cutoffChoose_ratio (d p k : ℕ) (hk : k ≤ p) :
    ((d+p).choose (p-k) : ℝ) / (featureDimension d p : ℝ) =
      ∏ j ∈ Finset.range k, ((p-j : ℕ) : ℝ) / (d+1+j) := by
  have hD : (featureDimension d p : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_ne_zero (by omega : p ≤ d+p))
  induction k with
  | zero => change (featureDimension d p : ℝ) / (featureDimension d p : ℝ) = 1; exact div_self hD
  | succ k ih =>
    have hk' : k < p := by omega
    rw [Finset.prod_range_succ,← ih (by omega),cutoffChoose_step d p k hk']
    rw [Nat.cast_sub hk'.le]
    field_simp
    ring

lemma cutoff_factor_bound (d p j : ℕ) (hd : 1 ≤ d) (hj : j < p) :
    (4 * ((d:ℝ)/2+j)) * ((((p-j : ℕ) : ℝ)/(d+1+j))^2) ≤ 2*(p:ℝ)^2/d := by
  have hd' : (0:ℝ) < d := by exact_mod_cast hd
  have hden : (0:ℝ) < d+1+j := by positivity
  have hpj : ((p-j : ℕ) : ℝ) ≤ p := by exact_mod_cast Nat.sub_le p j
  have hpj0 : (0:ℝ) ≤ ((p-j : ℕ) : ℝ) := by positivity
  have hbase : 2*(d:ℝ)*((d:ℝ)/2+j) ≤ (d+1+j)^2 := by
    nlinarith [sq_nonneg ((j:ℝ)+1)]
  have hsq : (((p-j : ℕ) : ℝ))^2 ≤ (p:ℝ)^2 := pow_le_pow_left₀ hpj0 hpj 2
  apply (le_div_iff₀ hd').mpr
  have hden2 : 0 < (d+1+j:ℝ)^2 := sq_pos_of_pos hden
  rw [div_pow]
  calc
    _ = (4*((d:ℝ)/2+j)*(((p-j : ℕ) : ℝ)^2)*(d:ℝ))/(d+1+j)^2 := by ring
    _ ≤ 2*(p:ℝ)^2 := by
      apply (div_le_iff₀ hden2).mpr
      nlinarith [mul_nonneg (sub_nonneg.mpr hbase) (sq_nonneg (p:ℝ)),
    mul_nonneg (sub_nonneg.mpr hsq) (by positivity : 0 ≤ 4*(d:ℝ)*((d:ℝ)/2+j))]
end PrivateAgnosticHalfspace.Gaussian

end
section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
lemma cutoff_candidate_term_ratio (d p k : ℕ) (hk : k ≤ p) :
    ((4:ℝ)^k * Ring.multichoose ((d:ℝ)/2) k * shiftedChoose d k p * shiftedChoose d k p) /
      (featureDimension d p : ℝ)^2 =
    (∏ j ∈ Finset.range k, 4*((d:ℝ)/2+j)*((((p-j:ℕ):ℝ)/(d+1+j))^2)) / k.factorial := by
  rw [shiftedChoose,if_pos hk]
  have hr := cutoffChoose_ratio d p k hk
  have hprod : (4:ℝ)^k * (∏ j ∈ Finset.range k, ((d:ℝ)/2+j)) *
      (∏ j ∈ Finset.range k, (((p-j:ℕ):ℝ)/(d+1+j)))^2 =
      ∏ j ∈ Finset.range k, 4*((d:ℝ)/2+j)*((((p-j:ℕ):ℝ)/(d+1+j))^2) := by
    rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_range,Finset.prod_pow]
  calc
    _ = ((4:ℝ)^k * Ring.multichoose ((d:ℝ)/2) k) *
      (((d+p).choose (p-k) : ℝ)/(featureDimension d p : ℝ))^2 := by ring
    _ = ((4:ℝ)^k * ((∏ j ∈ Finset.range k, ((d:ℝ)/2+j))/k.factorial)) *
      (∏ j ∈ Finset.range k, (((p-j:ℕ):ℝ)/(d+1+j)))^2 := by rw [hr,multichoose_eq_product]
    _ = _ := by rw [←hprod]; ring

lemma cutoff_candidate_term_bound (d p k : ℕ) (hd : 1 ≤ d) (hk : k ≤ p) :
    (4:ℝ)^k * Ring.multichoose ((d:ℝ)/2) k * shiftedChoose d k p * shiftedChoose d k p ≤
      (featureDimension d p : ℝ)^2 * ((2*(p:ℝ)^2/d)^k/k.factorial) := by
  have hD : (0:ℝ) < featureDimension d p := by
    change (0:ℝ) < ((d+p).choose p : ℝ)
    exact_mod_cast Nat.choose_pos (by omega : p ≤ d+p)
  rw [mul_comm ((featureDimension d p : ℝ)^2)]
  apply (div_le_iff₀ (sq_pos_of_pos hD)).mp
  rw [cutoff_candidate_term_ratio d p k hk]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  calc
    _ ≤ ∏ j ∈ Finset.range k, (2*(p:ℝ)^2/d) := by
      apply Finset.prod_le_prod
      · intro j hj; positivity
      · intro j hj
        exact cutoff_factor_bound d p j hd (lt_of_lt_of_le (Finset.mem_range.mp hj) hk)
    _ = _ := by simp only [Finset.prod_const,Finset.card_range]

lemma cutoff_candidate_diagonal_bound (d p : ℕ) (hd : 1 ≤ d) :
    cutoffCandidate d p p ≤ Real.exp (2*(p:ℝ)^2/d) * (featureDimension d p : ℝ)^2 := by
  have ht : 0 ≤ 2*(p:ℝ)^2/d := by positivity
  have hs : HasSum (fun k : ℕ => (2*(p:ℝ)^2/d)^k/k.factorial) (Real.exp (2*(p:ℝ)^2/d)) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp (2*(p:ℝ)^2/d)
  have hsum : (∑ k ∈ Finset.range (p+1), (2*(p:ℝ)^2/d)^k/k.factorial) ≤ Real.exp (2*(p:ℝ)^2/d) := by
    rw [←hs.tsum_eq]
    exact hs.summable.sum_le_tsum (Finset.range (p+1)) (fun k _ => by positivity)
  unfold cutoffCandidate
  rw [tsum_eq_sum (s := Finset.range (p+1))]
  · calc
      _ ≤ ∑ k ∈ Finset.range (p+1), (featureDimension d p : ℝ)^2 *
          ((2*(p:ℝ)^2/d)^k/k.factorial) := by
        apply Finset.sum_le_sum
        intro k hk
        exact cutoff_candidate_term_bound d p k hd (by have := Finset.mem_range.mp hk; omega)
      _ = (featureDimension d p : ℝ)^2 * ∑ k ∈ Finset.range (p+1), (2*(p:ℝ)^2/d)^k/k.factorial :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hsum (sq_nonneg (featureDimension d p : ℝ))]
  · intro k hk
    have hkp : ¬ k ≤ p := by intro hle; exact hk (Finset.mem_range.mpr (by omega))
    simp only [shiftedChoose,if_neg hkp,mul_zero]
end PrivateAgnosticHalfspace.Gaussian

end
section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false
open PrivateAgnosticHalfspace.Gaussian in
theorem solution (d p : ℕ) (hd : 1 ≤ d) (hp : 1 ≤ p)
    (α : ℝ) (hα : 0 < α ∧ α < 1) (hdim : (d : ℝ) ≥ 2*(p:ℝ)^2/α) :
    (gaussian d).real {x | ‖features d p x‖ > 2*Real.sqrt (featureDimension d p)} ≤ α := by
  apply clipping_tail_from_fourth d p hd α hα hdim
  have he : (fun x : Vec d => ‖features d p x‖^4) =
      (fun x => ‖features d p x‖^2 * ‖features d p x‖^2) := by funext x; ring
  rw [he,cutoff_second_moment_formula]
  exact cutoff_candidate_diagonal_bound d p hd

end
