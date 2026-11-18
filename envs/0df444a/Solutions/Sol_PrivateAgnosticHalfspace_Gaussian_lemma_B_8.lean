-- Prove2me | solution 1 for PrivateAgnosticHalfspace.Gaussian.lemma_B_8
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T21:21:53.331194+00:00
-- url     : https://prove2.me/submissions/c6e20e32-3990-4db0-989a-1bdae2ab2667

import Definitions.Def_PrivateAgnosticHalfspace_Gaussian_Regression
import Definitions.Def_ChapterHermiteProductBasis
import Theorems.Thm_OAI_FiniteEntropySeparation_hermite_orthogonality
import Theorems.Thm_PrivateAgnosticHalfspace_Gaussian_finite_hermite_spanning_dimension

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

open MeasureTheory ProbabilityTheory Polynomial
open scoped BigOperators ENNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace PrivateAgnosticHalfspace.Gaussian
open BookProof.HermiteCore BookProof.HermiteProductCore BookProof.HermiteProductBasis
noncomputable def hermiteNormalizer {d : ℕ} (a : Fin d →₀ ℕ) : ℝ :=
  ∏ i : Fin d, Real.sqrt ((a i).factorial : ℝ)

lemma hermiteNormalizer_pos {d : ℕ} (a : Fin d →₀ ℕ) : 0 < hermiteNormalizer a := by
  apply Finset.prod_pos
  intro i _
  apply Real.sqrt_pos.mpr
  exact_mod_cast Nat.factorial_pos (a i)

lemma hermiteFun_eq_normalized (n : ℕ) (x : ℝ) :
    hermiteFun n x = Real.sqrt (n.factorial : ℝ) * AMPLowDeg.RankOne.hermNorm n x * gaussH x := by
  unfold hermiteFun hermiteR AMPLowDeg.RankOne.hermNorm
  have hn : Real.sqrt (n.factorial : ℝ) ≠ 0 := by positivity
  field_simp

lemma pgFun_hermite_normalized {d : ℕ} (a : Fin d →₀ ℕ) (x : Vec d) :
    pgFun (hermiteMv a) x =
      ((hermiteNormalizer a * hermite d (fun i => a i) x * gaussD x : ℝ) : ℂ) := by
  rw [pgFun_hermiteMv]
  congr 1
  unfold hermiteNormalizer hermite
  rw [gaussD_eq_prod, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  exact hermiteFun_eq_normalized (a i) (x i)

lemma memLp_hermite (d : ℕ) (κ : Fin d → ℕ) : MemLp (hermite d κ) 2 (gaussian d) := by
  let a : Fin d →₀ ℕ := Finsupp.equivFunOnFinite.symm κ
  have ha : (fun i => a i) = κ := Finsupp.equivFunOnFinite.apply_symm_apply κ
  have hpg := ((memLp_pgFun (hermiteMv a)).re).const_mul (hermiteNormalizer a)⁻¹
  apply gaussian_memLp_of_weighted d (hermite d κ)
  apply MemLp.ae_eq _ hpg
  apply ae_of_all
  intro x
  change (hermiteNormalizer a)⁻¹ * (pgFun (hermiteMv a) x).re = hermite d κ x * gaussD x
  rw [pgFun_hermite_normalized, Complex.ofReal_re, ha]
  field_simp [(hermiteNormalizer_pos a).ne']
end PrivateAgnosticHalfspace.Gaussian
namespace PrivateAgnosticHalfspace.Gaussian
lemma integral_hermNorm_mul (m n : ℕ) :
    (∫ x, AMPLowDeg.RankOne.hermNorm m x * AMPLowDeg.RankOne.hermNorm n x ∂gaussianReal 0 1) =
      if m = n then 1 else 0 := by
  unfold AMPLowDeg.RankOne.hermNorm
  simp only [div_mul_div_comm, ← Polynomial.eval_mul]
  rw [integral_div, OAI.FiniteEntropySeparation.hermite_orthogonality]
  by_cases h : m = n
  · subst n
    rw [if_pos rfl, Real.mul_self_sqrt (Nat.cast_nonneg _)]
    simp [div_self (show (m.factorial : ℝ) ≠ 0 by positivity)]
  · simp [h]

lemma hermite_integrable_mul (d : ℕ) (κ ξ : Fin d → ℕ) :
    Integrable (fun x => hermite d κ x * hermite d ξ x) (gaussian d) :=
  (memLp_hermite d κ).integrable_mul (memLp_hermite d ξ)

lemma integral_hermite_mul (d : ℕ) (κ ξ : Fin d → ℕ) :
    (∫ x, hermite d κ x * hermite d ξ x ∂gaussian d) = if κ = ξ then 1 else 0 := by
  classical
  rw [gaussian, ← map_pi_eq_stdGaussian]
  rw [integral_map (by fun_prop)]
  · change (∫ x : Fin d → ℝ,
        (∏ i, AMPLowDeg.RankOne.hermNorm (κ i) (x i)) *
        (∏ i, AMPLowDeg.RankOne.hermNorm (ξ i) (x i)) ∂Measure.pi (fun _ => gaussianReal 0 1)) = _
    simp_rw [← Finset.prod_mul_distrib]
    rw [integral_fintype_prod_eq_prod (fun i t =>
      AMPLowDeg.RankOne.hermNorm (κ i) t * AMPLowDeg.RankOne.hermNorm (ξ i) t)
      (μ := fun _ : Fin d => gaussianReal 0 1)]
    simp_rw [integral_hermNorm_mul]
    by_cases h : κ = ξ
    · subst ξ
      simp
    · rw [if_neg h]
      have hne : ∃ i, κ i ≠ ξ i := by
        by_contra hh
        push_neg at hh
        exact h (funext hh)
      obtain ⟨i,hi⟩ := hne
      exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
  · unfold hermite AMPLowDeg.RankOne.hermNorm
    fun_prop
end PrivateAgnosticHalfspace.Gaussian
namespace PrivateAgnosticHalfspace.Gaussian
noncomputable def gaussianHermiteLp (d : ℕ) (κ : Fin d → ℕ) : Lp ℝ 2 (gaussian d) :=
  (memLp_hermite d κ).toLp (hermite d κ)

lemma gaussianHermiteLp_coe (d : ℕ) (κ : Fin d → ℕ) :
    (gaussianHermiteLp d κ : Vec d → ℝ) =ᵐ[gaussian d] hermite d κ :=
  (memLp_hermite d κ).coeFn_toLp

lemma orthonormal_gaussianHermiteLp (d : ℕ) : Orthonormal ℝ (gaussianHermiteLp d) := by
  rw [orthonormal_iff_ite]
  intro κ ξ
  rw [L2.inner_def]
  calc
    _ = ∫ x, hermite d κ x * hermite d ξ x ∂gaussian d := by
      apply integral_congr_ae
      filter_upwards [gaussianHermiteLp_coe d κ, gaussianHermiteLp_coe d ξ] with x hκ hξ
      simp [hκ,hξ, RCLike.inner_apply]
      <;> ring
    _ = _ := integral_hermite_mul d κ ξ

lemma integral_gaussian_weighted (d : ℕ) (f : Vec d → ℝ) :
    (∫ x, f x ∂gaussian d) = ∫ x, gaussianWeight d x * f x ∂volume := by
  rw [gaussian_eq_withDensity]
  have hh := integral_withDensity_eq_integral_toReal_smul
    (continuous_gaussianWeight d).measurable.ennreal_ofReal
    (by simp : ∀ᵐ x ∂(volume : Measure (Vec d)), ENNReal.ofReal (gaussianWeight d x) < ∞) f
  simpa only [ENNReal.toReal_ofReal (gaussianWeight_pos d _).le, smul_eq_mul] using hh
end PrivateAgnosticHalfspace.Gaussian
namespace PrivateAgnosticHalfspace.Gaussian
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
lemma gaussianHermite_total (d : ℕ) (u : Lp ℝ 2 (gaussian d))
    (horth : ∀ κ, inner ℝ (gaussianHermiteLp d κ) u = 0) : u = 0 := by
  have hf := gaussian_memLp_weighted d (u : Vec d → ℝ) (Lp.memLp u)
  have hfc : MemLp (fun x : Vec d => ((u x * gaussD x : ℝ) : ℂ)) 2 volume := hf.ofReal
  let U : Lp ℂ 2 (volume : Measure (Vec d)) := hfc.toLp _
  have hUcoe : (U : Vec d → ℂ) =ᵐ[volume] (fun x => ((u x * gaussD x : ℝ) : ℂ)) := hfc.coeFn_toLp
  have hz (κ : Fin d → ℕ) : (∫ x, u x * hermite d κ x ∂gaussian d) = 0 := by
    calc
      _ = inner ℝ (gaussianHermiteLp d κ) u := by
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [gaussianHermiteLp_coe d κ] with x hx
        simp [hx, RCLike.inner_apply]
        <;> ring
      _ = 0 := horth κ
  have hzvol (κ : Fin d → ℕ) :
      (∫ x : Vec d, (u x * hermite d κ x) * gaussD x ^ 2) = 0 := by
    have hh := hz κ
    rw [integral_gaussian_weighted] at hh
    have heq : (∫ x : Vec d, gaussianWeight d x * (u x * hermite d κ x)) =
        densityConstant d * ∫ x : Vec d, (u x * hermite d κ x) * gaussD x ^ 2 := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact ae_of_all _ (fun x => by dsimp only; rw [gaussianWeight_eq_gaussD]; ring)
    rw [heq] at hh
    exact (mul_eq_zero.mp hh).resolve_left (densityConstant_pos d).ne'
  have hpg (a : Fin d →₀ ℕ) : inner ℂ (pgLp (hermiteMv a)) U = 0 := by
    calc
      _ = ∫ x : Vec d,
          ((hermiteNormalizer a * ((u x * hermite d (fun i => a i) x) * gaussD x ^ 2) : ℝ) : ℂ) := by
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [pgLp_coeFn (hermiteMv a), hUcoe] with x hx hux
        rw [hx, hux, pgFun_hermite_normalized]
        simp only [RCLike.inner_apply, Complex.conj_ofReal]
        push_cast
        ring
      _ = ((hermiteNormalizer a * ∫ x : Vec d,
          (u x * hermite d (fun i => a i) x) * gaussD x ^ 2 : ℝ) : ℂ) := by
        rw [integral_complex_ofReal, integral_const_mul]
      _ = 0 := by rw [hzvol, mul_zero, Complex.ofReal_zero]
  have hUz : U = 0 := by
    apply (hermiteMvBasis (d := d)).repr.injective
    ext a
    rw [HilbertBasis.repr_apply_apply, HilbertBasis.repr_apply_apply, inner_zero_right]
    simp only [hermiteMvBasis, HilbertBasis.coe_mk]
    change inner ℂ (hermiteMvLp a) U = 0
    rw [hermiteMvLp, inner_smul_left, hpg, mul_zero]
  have hwzero : (fun x : Vec d => ((u x * gaussD x : ℝ) : ℂ)) =ᵐ[volume] 0 := by
    exact hUcoe.symm.trans (hUz ▸ (Lp.coeFn_zero ℂ 2 (volume : Measure (Vec d))))
  have hrealzero : (u : Vec d → ℝ) =ᵐ[volume] 0 := by
    filter_upwards [hwzero] with x hx
    have hh : u x * gaussD x = 0 := Complex.ofReal_eq_zero.mp hx
    exact (mul_eq_zero.mp hh).resolve_right (gaussD_ne_zero x)
  apply Lp.ext
  exact ((gaussian_absolutelyContinuous_volume d).ae_eq hrealzero).trans (Lp.coeFn_zero ℝ 2 (gaussian d)).symm

lemma gaussianHermite_basis_exists (d : ℕ) :
    ∃ b : HilbertBasis (Fin d → ℕ) ℝ (Lp ℝ 2 (gaussian d)),
      ∀ κ, (fun x => (b κ) x) =ᵐ[gaussian d] hermite d κ := by
  have hbot : (Submodule.span ℝ (Set.range (gaussianHermiteLp d)))ᗮ = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro u hu
    apply gaussianHermite_total d u
    intro κ
    have hs : gaussianHermiteLp d κ ∈ Submodule.span ℝ (Set.range (gaussianHermiteLp d)) :=
      Submodule.subset_span ⟨κ,rfl⟩
    exact Submodule.inner_right_of_mem_orthogonal hs hu
  let b := HilbertBasis.mk (orthonormal_gaussianHermiteLp d)
    (Submodule.topologicalClosure_eq_top_iff.mpr hbot).ge
  refine ⟨b, ?_⟩
  intro κ
  simpa only [b, HilbertBasis.coe_mk] using gaussianHermiteLp_coe d κ
end PrivateAgnosticHalfspace.Gaussian

open MeasureTheory ProbabilityTheory Polynomial
open scoped BigOperators ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
noncomputable def hermiteComplex (n : ℕ) : Polynomial ℂ :=
  (Polynomial.hermite n).map (Int.castRingHom ℂ)

lemma hermiteComplex_succ (n : ℕ) :
    hermiteComplex (n + 1) = Polynomial.X * hermiteComplex n - (hermiteComplex n).derivative := by
  simp only [hermiteComplex, Polynomial.hermite_succ, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_X, Polynomial.derivative_map]

lemma generating_derivative (x : ℂ) (n : ℕ) (t : ℂ) :
    HasDerivAt (fun z => (hermiteComplex n).eval (x - z) * Complex.exp (z * x - z ^ 2 / 2))
      ((hermiteComplex (n + 1)).eval (x - t) * Complex.exp (t * x - t ^ 2 / 2)) t := by
  have hp := ((hermiteComplex n).hasDerivAt (x - t)).comp t ((hasDerivAt_const t x).sub (hasDerivAt_id t))
  have he := ((((hasDerivAt_id t).mul_const x).sub (((hasDerivAt_id t).pow 2).div_const 2))).cexp
  have hh := hp.mul he
  convert! hh using 1
  rw [hermiteComplex_succ]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X,
    Function.comp_apply, Pi.sub_apply, Pi.pow_apply, id_eq, Nat.reduceSub, pow_one]
  ring

lemma iteratedDeriv_generating (x : ℂ) (n : ℕ) :
    iteratedDeriv n (fun z => Complex.exp (z * x - z ^ 2 / 2)) =
      fun t => (hermiteComplex n).eval (x - t) * Complex.exp (t * x - t ^ 2 / 2) := by
  induction n with
  | zero =>
    funext t
    simp [hermiteComplex, Polynomial.hermite_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    exact (generating_derivative x n t).deriv

lemma hermite_generating_complex (x t : ℂ) :
    HasSum (fun n : ℕ => (hermiteComplex n).eval x * t ^ n / n.factorial)
      (Complex.exp (t * x - t ^ 2 / 2)) := by
  have hf : Differentiable ℂ (fun z : ℂ => Complex.exp (z * x - z ^ 2 / 2)) := by fun_prop
  have hh := Complex.hasSum_taylorSeries_of_entire hf 0 t
  simp only [iteratedDeriv_generating, sub_zero, zero_mul, zero_pow (by norm_num : 2 ≠ 0),
    zero_div, sub_self, Complex.exp_zero, mul_one, smul_eq_mul] at hh
  convert! hh using 1
  funext n
  ring

end PrivateAgnosticHalfspace.Gaussian
namespace PrivateAgnosticHalfspace.Gaussian
lemma hermiteComplex_eval_real (n : ℕ) (x : ℝ) :
    (hermiteComplex n).eval (x : ℂ) =
      ((((Polynomial.hermite n).map (Int.castRingHom ℝ)).eval x : ℝ) : ℂ) := by
  have hm : Int.castRingHom ℂ = Complex.ofRealHom.comp (Int.castRingHom ℝ) := by
    ext z
    simp
  change (hermiteComplex n).eval (Complex.ofRealHom x) = _
  rw [hermiteComplex, hm, ← Polynomial.map_map, Polynomial.eval_map_apply]
  rfl

lemma hermite_generating_real (x t : ℝ) :
    HasSum (fun n : ℕ => AMPLowDeg.RankOne.hermNorm n x * t ^ n / Real.sqrt (n.factorial))
      (Real.exp (t * x - t ^ 2 / 2)) := by
  have hh := Complex.hasSum_re (hermite_generating_complex (x : ℂ) (t : ℂ))
  simp only [hermiteComplex_eval_real, ← Complex.ofReal_natCast, ← Complex.ofReal_pow,
    ← Complex.ofReal_mul, ← Complex.ofReal_sub, ← Complex.ofReal_div,
    ← Complex.ofReal_ofNat, ← Complex.ofReal_exp, Complex.ofReal_re] at hh
  convert! hh using 1
  funext n
  unfold AMPLowDeg.RankOne.hermNorm
  rw [div_mul_eq_mul_div, div_div, Real.mul_self_sqrt (Nat.cast_nonneg _)]
end PrivateAgnosticHalfspace.Gaussian

open PrivateAgnosticHalfspace.Gaussian


theorem solution (d : ℕ) :
    (∀ x t : ℝ, HasSum
      (fun m : ℕ => AMPLowDeg.RankOne.hermNorm m x * t ^ m / Real.sqrt (m.factorial))
      (Real.exp (t * x - t ^ 2 / 2))) ∧
    (∀ κ : Fin d → ℕ, MemLp (hermite d κ) 2 (gaussian d)) ∧
    (∃ b : HilbertBasis (Fin d → ℕ) ℝ (Lp ℝ 2 (gaussian d)),
      ∀ κ, (fun x => (b κ) x) =ᵐ[gaussian d] hermite d κ) ∧
    (∀ p, polynomialFunctions d p = Set.range (polynomialPredictor d p) ∧
      Fintype.card (Index d p) = featureDimension d p ∧
      (∀ κ ξ : Index d p,
        Integrable (fun x => hermite d (fun i => (κ.val i).val) x *
          hermite d (fun i => (ξ.val i).val) x) (gaussian d) ∧
        (∫ x, hermite d (fun i => (κ.val i).val) x *
          hermite d (fun i => (ξ.val i).val) x ∂gaussian d) = if κ = ξ then 1 else 0)) := by
  refine ⟨hermite_generating_real, memLp_hermite d, gaussianHermite_basis_exists d, ?_⟩
  intro p
  obtain ⟨hspan,hcard⟩ := finite_hermite_spanning_dimension d p
  refine ⟨hspan,hcard,?_⟩
  intro κ ξ
  refine ⟨hermite_integrable_mul d _ _, ?_⟩
  have heq : (fun i => (κ.val i).val) = (fun i => (ξ.val i).val) ↔ κ = ξ := by
    constructor
    · intro h
      apply Subtype.ext
      funext i
      apply Fin.ext
      exact congrFun h i
    · intro h
      subst ξ
      rfl
  simpa only [heq] using integral_hermite_mul d (fun i => (κ.val i).val) (fun i => (ξ.val i).val)



