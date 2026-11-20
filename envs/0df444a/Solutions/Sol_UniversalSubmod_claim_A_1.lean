-- Prove2me | solution 1 for UniversalSubmod.claim_A_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:10:06.161691+00:00
-- url     : https://prove2.me/submissions/04cba200-c565-40d9-b440-7fbd73e17e4b

import Mathlib

section
set_option autoImplicit false
namespace UniversalSubmod.Dev.ClaimA1

open MeasureTheory ProbabilityTheory
open scoped NNReal Real

/-- One-dimensional Stein identity for a centered real Gaussian. -/
theorem stein (v : ℝ≥0) (h h' : ℝ → ℝ) (hd : ∀ x, HasDerivAt h (h' x) x)
    (hc : Continuous h') (C : ℝ) (hb : ∀ x, |h' x| ≤ C) :
    ∫ x, x * h x ∂(gaussianReal 0 v) = v * ∫ x, h' x ∂(gaussianReal 0 v) := by
  by_cases hv : v = 0
  · subst hv; simp [gaussianReal_zero_var]
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hb 0)
  have hdiff : Differentiable ℝ h := fun x => (hd x).differentiableAt
  have hderiv : deriv h = h' := funext fun x => (hd x).deriv
  have hlip : LipschitzWith C.toNNReal h := by
    apply lipschitzWith_of_nnnorm_deriv_le hdiff
    intro x
    rw [hderiv]
    have := hb x
    rw [← NNReal.coe_le_coe]
    simpa [Real.norm_eq_abs, Real.coe_toNNReal _ hC] using this
  have hbound : ∀ x, |h x| ≤ |h 0| + C * |x| := by
    intro x
    have := hlip.dist_le_mul x 0
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hC] at this
    have h2 : |h x| ≤ |h x - h 0| + |h 0| := by
      have := abs_sub_abs_le_abs_sub (h x) (h 0); linarith
    simp at this
    linarith
  have hmeas : Measurable h := hdiff.continuous.measurable
  set γ := gaussianReal 0 v with hγ
  have hid : MemLp id 2 γ := memLp_id_gaussianReal 2
  have hint1 : Integrable (fun x : ℝ => x) γ := by
    exact hid.integrable (by norm_num)
  have hint2 : Integrable (fun x : ℝ => x ^ 2) γ := by
    simpa using hid.integrable_sq
  have hih : Integrable h γ := by
    refine Integrable.mono' ((integrable_const (|h 0|)).add (hint1.norm.const_mul C)) hmeas.aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    simpa using hbound x
  have hixh : Integrable (fun x => x * h x) γ := by
    refine Integrable.mono' (((hint1.norm).const_mul (|h 0|)).add (hint2.const_mul C))
      (measurable_id.mul hmeas).aestronglyMeasurable (ae_of_all _ fun x => ?_)
    simp only [norm_mul, Real.norm_eq_abs, Pi.add_apply]
    have := hbound x
    have hx := abs_nonneg x
    calc |x| * |h x| ≤ |x| * (|h 0| + C * |x|) := by gcongr
      _ = |h 0| * |x| + C * x ^ 2 := by rw [← sq_abs x]; ring
  have hih' : Integrable h' γ := by
    refine Integrable.mono' (integrable_const C) hc.aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    simpa using hb x
  -- transfer to Lebesgue with density
  have tr : ∀ {f : ℝ → ℝ}, Integrable f γ ↔
      Integrable (fun x => gaussianPDFReal 0 v x * f x) volume := by
    intro f
    rw [hγ, gaussianReal_of_var_ne_zero _ hv,
      integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 v)
        (ae_of_all _ fun _ => gaussianPDF_lt_top)]
    simp [toReal_gaussianPDF]
  set φ := gaussianPDFReal 0 v with hφ
  have hφd : ∀ x, HasDerivAt φ (-(x / v) * φ x) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => -(x - 0) ^ 2 / (2 * (v : ℝ))) (-(2 * x) / (2 * v)) x := by
      have := ((hasDerivAt_id x).sub_const 0).pow 2 |>.neg.div_const (2 * (v : ℝ))
      simpa using this
    have := (h1.exp).const_mul (√(2 * π * v))⁻¹
    rw [hφ, gaussianPDFReal_def]
    refine this.congr_deriv ?_
    have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
    simp only [sub_zero]
    field_simp
  have hφ0 : ∀ x, 0 ≤ φ x := fun x => gaussianPDFReal_nonneg _ _ _
  have e1 : ∫ x, x * h x ∂γ = ∫ x, φ x * (x * h x) := by
    rw [hγ, integral_gaussianReal_eq_integral_smul hv]; rfl
  have e2 : ∫ x, h' x ∂γ = ∫ x, φ x * h' x := by
    rw [hγ, integral_gaussianReal_eq_integral_smul hv]; rfl
  have I1 : Integrable (fun x => h x * (-(x / v) * φ x)) := by
    have := (tr.1 hixh).const_mul (-(1 / (v : ℝ)))
    refine this.congr (ae_of_all _ fun x => ?_)
    simp only; ring
  have I2 : Integrable (fun x => h' x * φ x) := by
    have := tr.1 hih'
    refine this.congr (ae_of_all _ fun x => ?_)
    simp only; ring
  have I3 : Integrable (fun x => h x * φ x) := by
    have := tr.1 hih
    refine this.congr (ae_of_all _ fun x => ?_)
    simp only; ring
  have key := integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable
    (L := ContinuousLinearMap.mul ℝ ℝ) (u := h) (v := φ) (u' := h') (v' := fun x => -(x / v) * φ x)
    (fun x _ => hd x) (fun x _ => hφd x) (by simpa using I1) (by simpa using I2) (by simpa using I3)
  simp only [ContinuousLinearMap.mul_apply'] at key
  rw [e1, e2]
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  have : ∫ x, φ x * (x * h x) = - (v : ℝ) * ∫ x, h x * (-(x / v) * φ x) := by
    rw [← integral_const_mul]
    congr 1; ext x; field_simp
  rw [this, key]
  have : ∫ x, h' x * φ x = ∫ x, φ x * h' x := by congr 1; ext x; ring
  rw [this]; ring


section Multi

variable {n : ℕ} (g : (Fin n → ℝ) → ℝ)

theorem fderiv_apply_eq_sum (y a : Fin n → ℝ) :
    fderiv ℝ g y a = ∑ j, a j * fderiv ℝ g y (Pi.single j (1 : ℝ)) := by
  have h : a = ∑ j, a j • (Pi.single j (1 : ℝ) : Fin n → ℝ) := by
    ext i; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [h]
  simp [map_sum]

theorem growth (hg : ContDiff ℝ 1 g) (C : ℝ)
    (hgb : ∀ x j, |fderiv ℝ g x (Pi.single j (1 : ℝ))| ≤ C) (x : Fin n → ℝ) :
    |g x| ≤ |g 0| + (n * C) * ∑ j, |x j| := by
  have hC : 0 ≤ C ∨ n = 0 := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exact Or.inr h
    · exact Or.inl (le_trans (abs_nonneg _) (hgb 0 ⟨0, h⟩))
  have hC' : 0 ≤ (n : ℝ) * C := by
    rcases hC with h | h
    · positivity
    · subst h; simp
  have hdiff : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hop : ∀ y, ‖fderiv ℝ g y‖ ≤ n * C := by
    intro y
    refine ContinuousLinearMap.opNorm_le_bound _ hC' fun z => ?_
    rw [Real.norm_eq_abs, fderiv_apply_eq_sum]
    calc |∑ j, z j * fderiv ℝ g y (Pi.single j (1 : ℝ))|
        ≤ ∑ j, |z j * fderiv ℝ g y (Pi.single j (1 : ℝ))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin n, ‖z‖ * C := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [abs_mul]
          exact mul_le_mul (by simpa using norm_le_pi_norm z j) (hgb y j) (abs_nonneg _)
            (norm_nonneg _)
      _ = n * C * ‖z‖ := by simp; ring
  have hmv := (convex_univ (𝕜 := ℝ) (E := Fin n → ℝ)).norm_image_sub_le_of_norm_fderiv_le
    (fun y _ => hdiff y) (fun y _ => hop y) (Set.mem_univ 0) (Set.mem_univ x)
  have hnorm : ‖x‖ ≤ ∑ j, |x j| := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
    rw [Real.norm_eq_abs]
    exact Finset.single_le_sum (f := fun j => |x j|) (fun i _ => abs_nonneg _) (Finset.mem_univ j)
  rw [sub_zero, Real.norm_eq_abs] at hmv
  have := abs_sub_abs_le_abs_sub (g x) (g 0)
  have h3 : (n * C) * ‖x‖ ≤ (n * C) * ∑ j, |x j| := by gcongr
  linarith

end Multi


section Main

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {U : Ω → ℝ} {V : Fin n → Ω → ℝ}

theorem main_pos
    (hUV : HasGaussianLaw (fun ω => (U ω, fun j => V j ω)) P)
    (hU0 : ∫ ω, U ω ∂P = 0)
    (g : (Fin n → ℝ) → ℝ) (hg : ContDiff ℝ 1 g) (C : ℝ)
    (hgb : ∀ x j, |fderiv ℝ g x (Pi.single j (1 : ℝ))| ≤ C)
    (hv : 0 < Var[U; P]) :
    ∫ ω, U ω * g (fun j => V j ω) ∂P =
      ∑ j, cov[U, V j; P] * ∫ ω, fderiv ℝ g (fun l => V l ω) (Pi.single j (1 : ℝ)) ∂P := by
  classical
  set v : ℝ := Var[U; P] with hvdef
  have hUg : HasGaussianLaw U P := hUV.fst
  have hVg : HasGaussianLaw (fun ω j => V j ω) P := hUV.snd
  have hUm : AEMeasurable U P := hUg.aemeasurable
  have hVm : ∀ j, AEMeasurable (V j) P := fun j => (hVg.eval j).aemeasurable
  have hU2 : MemLp U 2 P := hUg.memLp_two
  have hV2 : ∀ j, MemLp (V j) 2 P := fun j => (hVg.eval j).memLp_two
  set a : Fin n → ℝ := fun j => cov[U, V j; P] / v with hadef
  set W : Fin n → Ω → ℝ := fun j ω => V j ω - a j * U ω with hWdef
  have hWm : ∀ j, AEMeasurable (W j) P := fun j => (hVm j).sub (hUm.const_mul _)
  have hW2 : ∀ j, MemLp (W j) 2 P := fun j => (hV2 j).sub (hU2.const_mul _)
  -- independence
  have hcovW : ∀ j, cov[U, W j; P] = 0 := by
    intro j
    have h1 : cov[U, W j; P] = cov[U, V j; P] - cov[U, fun ω => a j * U ω; P] :=
      covariance_fun_sub_right hU2 (hV2 j) (hU2.const_mul _)
    rw [h1, covariance_const_mul_right, covariance_self hUm]
    simp only [hadef]
    field_simp
    ring
  have hindep : IndepFun U (fun ω j => W j ω) P := by
    let L₀ : ℝ × (Fin n → ℝ) →ₗ[ℝ] (Unit → ℝ) × (Fin n → ℝ) :=
      { toFun := fun p => (fun _ => p.1, fun j => p.2 j - a j * p.1)
        map_add' := by intro p q; ext <;> simp <;> ring
        map_smul' := by intro c p; ext <;> simp <;> ring }
    let L : ℝ × (Fin n → ℝ) →L[ℝ] (Unit → ℝ) × (Fin n → ℝ) := LinearMap.toContinuousLinearMap L₀
    have hG : HasGaussianLaw (fun ω => (fun _ : Unit => U ω, fun j => W j ω)) P :=
      hUV.map_fun L
    have := HasGaussianLaw.indepFun_of_covariance_eval (X := fun (_ : Unit) => U) (Y := W) hG
      (fun _ j => hcovW j)
    have h2 := this.comp (φ := fun f : Unit → ℝ => f ()) (ψ := id) (show Measurable (fun f : Unit → ℝ => f ()) from measurable_pi_apply ()) measurable_id
    exact h2
  have hvne : v ≠ 0 := hv.ne'
  have hWm' : AEMeasurable (fun ω j => W j ω) P := aemeasurable_pi_iff.2 hWm
  have hVm' : AEMeasurable (fun ω j => V j ω) P := aemeasurable_pi_iff.2 hVm
  have hmap : P.map (fun ω => (U ω, fun j => W j ω)) = (P.map U).prod (P.map (fun ω j => W j ω)) :=
    (indepFun_iff_map_prod_eq_prod_map_map hUm hWm').1 hindep
  have hγ : P.map U = gaussianReal 0 v.toNNReal := by
    rw [hUg.map_eq_gaussianReal, hU0]
  have hvnn : ((v.toNNReal : ℝ≥0) : ℝ) = v := Real.coe_toNNReal _ hv.le
  have hVW : ∀ ω j, V j ω = W j ω + a j * U ω := by intro ω j; simp [hWdef]
  set f : ℝ × (Fin n → ℝ) → ℝ := fun p => p.1 * g (fun j => p.2 j + a j * p.1) with hfdef
  set F' : ℝ × (Fin n → ℝ) → ℝ :=
    fun p => fderiv ℝ g (fun j => p.2 j + a j * p.1) a with hF'def
  have hgc : Continuous g := hg.continuous
  have hdgc : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by norm_num)
  have hfc : Continuous f := by
    simp only [hfdef]; fun_prop
  have hF'c : Continuous F' := by
    simp only [hF'def]
    exact (hdgc.clm_apply continuous_const).comp (by fun_prop : Continuous
      (fun p : ℝ × (Fin n → ℝ) => (fun j => p.2 j + a j * p.1)))
  have hpt : ∀ ω, (U ω, fun j => W j ω) = (U ω, fun j => W j ω) := fun _ => rfl
  have hfU : ∀ ω, f (U ω, fun j => W j ω) = U ω * g (fun j => V j ω) := by
    intro ω
    simp only [hfdef]
    congr 2
    ext j; rw [hVW ω j]
  have hF'U : ∀ ω, F' (U ω, fun j => W j ω) = fderiv ℝ g (fun l => V l ω) a := by
    intro ω
    simp only [hF'def]
    congr 2
    ext j; rw [hVW ω j]
  -- integrability of U * g(V)
  have hint0 : Integrable (fun ω => U ω * g (fun j => V j ω)) P := by
    have hb : Integrable (fun ω => |g 0| * |U ω| + ((n : ℝ) * C) * ∑ j, |U ω| * |V j ω|) P := by
      refine ((hU2.integrable (by norm_num)).norm.const_mul _).add ?_
      refine Integrable.const_mul (integrable_finsetSum _ fun j _ => ?_) _
      exact ((hU2.integrable_mul (hV2 j)).norm).congr (ae_of_all _ fun ω => by simp)
    refine Integrable.mono' hb ?_ (ae_of_all _ fun ω => ?_)
    · exact hUm.aestronglyMeasurable.mul
        (hgc.measurable.comp_aemeasurable hVm').aestronglyMeasurable
    · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have := growth g hg C hgb (fun j => V j ω)
      have hC : 0 ≤ (n : ℝ) * C := by
        rcases Nat.eq_zero_or_pos n with h | h
        · subst h; simp
        · exact mul_nonneg (by positivity) (le_trans (abs_nonneg _) (hgb 0 ⟨0, h⟩))
      calc |U ω| * |g fun j => V j ω| ≤ |U ω| * (|g 0| + (n * C) * ∑ j, |V j ω|) := by
            gcongr
        _ = |g 0| * |U ω| + ((n : ℝ) * C) * ∑ j, |U ω| * |V j ω| := by
            rw [← Finset.mul_sum]; ring
  have hAM : AEMeasurable (fun ω => (U ω, fun j => W j ω)) P := hUm.prodMk hWm'
  have hfint : Integrable f ((P.map U).prod (P.map (fun ω j => W j ω))) := by
    rw [← hmap, integrable_map_measure hfc.aestronglyMeasurable hAM]
    exact hint0.congr (ae_of_all _ fun ω => (hfU ω).symm)
  have hF'int : Integrable F' ((P.map U).prod (P.map (fun ω j => W j ω))) := by
    refine Integrable.mono' (integrable_const (∑ j, |a j| * C)) hF'c.aestronglyMeasurable
      (ae_of_all _ fun p => ?_)
    simp only [hF'def, Real.norm_eq_abs]
    rw [fderiv_apply_eq_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hgb _ j) (abs_nonneg _)
  have step1 : ∫ ω, U ω * g (fun j => V j ω) ∂P =
      ∫ p, f p ∂((P.map U).prod (P.map (fun ω j => W j ω))) := by
    rw [← hmap, integral_map hAM hfc.aestronglyMeasurable]
    exact integral_congr_ae (ae_of_all _ fun ω => (hfU ω).symm)
  have step2 : ∫ p, f p ∂((P.map U).prod (P.map (fun ω j => W j ω))) =
      ∫ w, v * ∫ u, F' (u, w) ∂(P.map U) ∂(P.map (fun ω j => W j ω)) := by
    rw [integral_prod_symm f hfint]
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    simp only [hfdef, hF'def]
    rw [hγ]
    have := stein v.toNNReal (fun u => g (fun j => w j + a j * u))
      (fun u => fderiv ℝ g (fun j => w j + a j * u) a) ?_ ?_ (∑ j, |a j| * C) ?_
    · rw [hvnn] at this; exact this
    · intro u
      have h1 : HasDerivAt (fun u : ℝ => (fun j => w j + a j * u : Fin n → ℝ)) a u := by
        refine hasDerivAt_pi.2 fun j => ?_
        simpa using ((hasDerivAt_id u).const_mul (a j)).const_add (w j)
      have h2 : HasFDerivAt g (fderiv ℝ g (fun j => w j + a j * u)) (fun j => w j + a j * u) :=
        ((hg.differentiable (by norm_num)) _).hasFDerivAt
      exact h2.comp_hasDerivAt u h1
    · exact (hdgc.clm_apply continuous_const).comp (by fun_prop : Continuous
        (fun u : ℝ => (fun j => w j + a j * u)))
    · intro u
      rw [fderiv_apply_eq_sum]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hgb _ j) (abs_nonneg _)
  have step3 : ∫ w, v * ∫ u, F' (u, w) ∂(P.map U) ∂(P.map (fun ω j => W j ω)) =
      v * ∫ ω, fderiv ℝ g (fun l => V l ω) a ∂P := by
    rw [integral_const_mul, ← integral_prod_symm F' hF'int, ← hmap,
      integral_map hAM hF'c.aestronglyMeasurable]
    congr 1
    exact integral_congr_ae (ae_of_all _ fun ω => hF'U ω)
  have hint_j : ∀ j, Integrable (fun ω => fderiv ℝ g (fun l => V l ω) (Pi.single j (1 : ℝ))) P := by
    intro j
    refine Integrable.mono' (integrable_const C) ?_ (ae_of_all _ fun ω => ?_)
    · exact ((hdgc.clm_apply continuous_const).measurable.comp_aemeasurable hVm').aestronglyMeasurable
    · simpa using hgb _ j
  have step4 : ∫ ω, fderiv ℝ g (fun l => V l ω) a ∂P =
      ∑ j, a j * ∫ ω, fderiv ℝ g (fun l => V l ω) (Pi.single j (1 : ℝ)) ∂P := by
    rw [integral_congr_ae (ae_of_all _ fun ω => fderiv_apply_eq_sum g (fun l => V l ω) a)]
    rw [integral_finsetSum _ fun j _ => (hint_j j).const_mul _]
    simp_rw [integral_const_mul]
  rw [step1, step2, step3, step4, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [hadef]
  field_simp

end Main

end UniversalSubmod.Dev.ClaimA1

namespace UniversalSubmod

open MeasureTheory ProbabilityTheory

theorem chk_claim_A_1 {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Ω → ℝ) (V : Fin n → Ω → ℝ)
    (hUV : HasGaussianLaw (fun ω => (U ω, fun j => V j ω)) P)
    (hU0 : ∫ ω, U ω ∂P = 0) (hV0 : ∀ j, ∫ ω, V j ω ∂P = 0)
    (g : (Fin n → ℝ) → ℝ) (hg : ContDiff ℝ 1 g)
    (hgb : ∃ C : ℝ, ∀ x j, |fderiv ℝ g x (Pi.single j (1 : ℝ))| ≤ C) :
    ∫ ω, U ω * g (fun j => V j ω) ∂P =
      ∑ j, cov[U, V j; P] * ∫ ω, fderiv ℝ g (fun l => V l ω) (Pi.single j (1 : ℝ)) ∂P := by
  obtain ⟨C, hC⟩ := hgb
  rcases (variance_nonneg U P).eq_or_lt with h0 | hpos
  · have hU2 : MemLp U 2 P := hUV.fst.memLp_two
    have hae : U =ᵐ[P] fun _ => P[U] :=
      ae_eq_integral_of_variance_eq_zero hU2 h0.symm
    have hae0 : U =ᵐ[P] fun _ => 0 := by rwa [hU0] at hae
    have hcov : ∀ j, cov[U, V j; P] = 0 := by
      intro j
      rw [covariance_eq_sub hU2 (hUV.snd.eval j).memLp_two, hU0, zero_mul, sub_zero]
      exact integral_eq_zero_of_ae (by
        filter_upwards [hae0] with ω hω; simp [hω])
    simp only [hcov, zero_mul, Finset.sum_const_zero]
    exact integral_eq_zero_of_ae (by
      filter_upwards [hae0] with ω hω; simp [hω])
  · exact Dev.ClaimA1.main_pos hUV hU0 g hg C hC hpos

end UniversalSubmod
end

theorem solution : type_of% @UniversalSubmod.chk_claim_A_1 := @UniversalSubmod.chk_claim_A_1
