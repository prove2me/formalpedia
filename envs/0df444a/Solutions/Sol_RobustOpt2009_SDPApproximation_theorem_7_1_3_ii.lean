-- Prove2me | solution 1 for RobustOpt2009.SDPApproximation.theorem_7_1_3_ii
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T06:49:27.550254+00:00
-- url     : https://prove2.me/submissions/4208184d-d0a0-42d1-8d2b-0ce5f6cea34c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ModernConvex_MatrixCube_MatrixCube
import Theorems.Thm_ModernConvex_MatrixCube_theta_bounds
import Theorems.Thm_ModernConvex_MatrixCube_gaussian_quadratic_form
import Theorems.Thm_RobustOpt2009_SDPApproximation_proposition_B_4_12
import Theorems.Thm_RobustOpt2009_SDPApproximation_theta_four


open Matrix MeasureTheory
open ModernConvex.MatrixCube




open Matrix MeasureTheory
open ModernConvex.MatrixCube

namespace MC99

open ProbabilityTheory

noncomputable def gB_phi (x : ℝ) : ℝ := gaussianPDFReal 0 1 x

lemma gB_phi_eq (x : ℝ) : gB_phi x = (2 * Real.pi) ^ (-(1 : ℝ) / 2) * Real.exp (-x ^ 2 / 2) := by
  simp only [gB_phi, gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (by positivity)]
  norm_num

lemma gB_density {ι : Type*} [Fintype ι] (u : ι → ℝ) :
    (2 * Real.pi) ^ (-(Fintype.card ι : ℝ) / 2) * Real.exp (-(∑ i, u i ^ 2) / 2) =
      ∏ i, gB_phi (u i) := by
  simp only [gB_phi_eq, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  congr 1
  · rw [← Real.rpow_mul_natCast (by positivity)]
    congr 1; ring
  · rw [← Real.exp_sum]; congr 1
    simp only [neg_div, Finset.sum_div, Finset.sum_neg_distrib]

lemma gB_gd (k : ℕ) (u : Fin k → ℝ) : gaussDensity k u = ∏ i, gB_phi (u i) := by
  rw [gaussDensity, ← gB_density, Fintype.card_fin]

lemma gB_int_phi (f : ℝ → ℝ) : ∫ x, f x * gB_phi x = ∫ x, f x ∂(gaussianReal 0 1) := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num)]
  simp only [smul_eq_mul, gB_phi]
  congr 1; funext x; ring

lemma gB_m0 : ∫ x, 1 * gB_phi x = 1 := by
  rw [gB_int_phi]; simp

lemma gB_m1 : ∫ x, x * gB_phi x = 0 := by
  rw [gB_int_phi]; exact integral_id_gaussianReal

lemma gB_m2 : ∫ x, x ^ 2 * gB_phi x = 1 := by
  rw [gB_int_phi]
  have h := variance_eq_integral (X := fun x : ℝ => x) (μ := gaussianReal 0 1) measurable_id.aemeasurable
  rw [variance_fun_id_gaussianReal, integral_id_gaussianReal] at h
  simp only [sub_zero] at h
  exact_mod_cast h.symm

lemma gB_phi_int_pow (m : ℕ) : Integrable (fun x : ℝ => x ^ m * gB_phi x) := by
  have := (integrable_rpow_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num) (s := m)
    (by have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith)).const_mul ((2 * Real.pi) ^ (-(1 : ℝ) / 2))
  refine this.congr (ae_of_all _ fun x => ?_)
  simp only [gB_phi_eq, Real.rpow_natCast]
  rw [show -(1 / 2 : ℝ) * x ^ 2 = -x ^ 2 / 2 by ring]
  ring

lemma gB_pair {n : ℕ} (i j : Fin n) :
    Integrable (fun u : Fin n → ℝ => u i * u j * gaussDensity n u) ∧
    ∫ u : Fin n → ℝ, u i * u j * gaussDensity n u = if i = j then 1 else 0 := by
  let g : Fin n → ℝ → ℝ := fun k x => (if k = i then x else 1) * (if k = j then x else 1) * gB_phi x
  have hfun : (fun u : Fin n → ℝ => u i * u j * gaussDensity n u) = fun u => ∏ k, g k (u k) := by
    funext u
    simp only [g, Finset.prod_mul_distrib, gB_gd, Finset.prod_ite_eq', Finset.mem_univ, if_true,
      Finset.prod_const_one]
  have hint : ∀ k, Integrable (g k) := by
    intro k
    by_cases hi : k = i <;> by_cases hj : k = j
    · simp only [g, if_pos hi, if_pos hj]; simpa [pow_two] using gB_phi_int_pow 2
    · simp only [g, if_pos hi, if_neg hj, mul_one]; simpa using gB_phi_int_pow 1
    · simp only [g, if_neg hi, if_pos hj, one_mul]; simpa using gB_phi_int_pow 1
    · simp only [g, if_neg hi, if_neg hj, one_mul]; simpa using gB_phi_int_pow 0
  rw [hfun]
  refine ⟨?_, ?_⟩
  · rw [volume_pi]; exact Integrable.fintype_prod hint
  · rw [volume_pi, integral_fintype_prod_eq_prod]
    split_ifs with hij
    · subst hij
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
      rw [Finset.prod_eq_one]
      · simp only [g, if_true, mul_one]; rw [← gB_m2]; congr 1; funext x; ring
      · intro k hk
        have : k ≠ i := Finset.ne_of_mem_erase hk
        simp only [g, this, if_false, mul_one, one_mul]
        simpa using gB_m0
    · refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      simp only [g, if_true, if_neg hij, mul_one]
      exact gB_m1

lemma gB_rotG {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℝ) (hU : Uᵀ * U = 1)
    (F : (ι → ℝ) → ℝ) (hF : Continuous F) :
    ∫ x, F (U *ᵥ x) = ∫ x, F x := by
  have hdet2 : U.det * U.det = 1 := by
    have := congrArg Matrix.det hU
    rwa [det_mul, det_transpose, det_one] at this
  have hdet : LinearMap.det (Matrix.toLin' U) ≠ 0 := by
    rw [LinearMap.det_toLin']; intro h; rw [h] at hdet2; simp at hdet2
  have habs : |(LinearMap.det (Matrix.toLin' U))⁻¹| = 1 := by
    rw [LinearMap.det_toLin', abs_inv]
    have : |U.det| * |U.det| = 1 := by rw [← abs_mul, hdet2, abs_one]
    have h0 : 0 ≤ |U.det| := abs_nonneg _
    have : |U.det| = 1 := by nlinarith
    rw [this, inv_one]
  have hmap : Measure.map (Matrix.toLin' U) volume = (volume : Measure (ι → ℝ)) := by
    rw [Real.map_linearMap_volume_pi_eq_smul_volume_pi hdet, habs, ENNReal.ofReal_one, one_smul]
  have hmeas : Measurable (Matrix.toLin' U) :=
    (LinearMap.continuous_of_finiteDimensional _).measurable
  calc ∫ x, F (U *ᵥ x) = ∫ x, F (Matrix.toLin' U x) := by simp [toLin'_apply]
    _ = ∫ x, F x ∂(Measure.map (Matrix.toLin' U) volume) :=
        (integral_map hmeas.aemeasurable hF.aestronglyMeasurable).symm
    _ = _ := by rw [hmap]

/-- product Gaussian density -/
noncomputable def gB_P {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ := ∏ i, gB_phi (x i)

lemma gB_phi_nonneg (x : ℝ) : 0 ≤ gB_phi x := gaussianPDFReal_nonneg _ _ _

lemma gB_P_nonneg {ι : Type*} [Fintype ι] (x : ι → ℝ) : 0 ≤ gB_P x :=
  Finset.prod_nonneg fun i _ => gB_phi_nonneg _

lemma gB_P_cont {ι : Type*} [Fintype ι] : Continuous (gB_P (ι := ι)) := by
  unfold gB_P; simp only [gB_phi_eq]; fun_prop

lemma gB_P_rot {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℝ) (hU : Uᵀ * U = 1) (x : ι → ℝ) :
    gB_P (U *ᵥ x) = gB_P x := by
  unfold gB_P
  rw [← gB_density, ← gB_density]
  have h : (U *ᵥ x) ⬝ᵥ (U *ᵥ x) = x ⬝ᵥ x := by
    rw [dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, hU, one_mulVec]
  have : ∑ i, (U *ᵥ x) i ^ 2 = ∑ i, x i ^ 2 := by simpa [dotProduct, pow_two] using h
  rw [this]

lemma gB_int_prod {ι : Type*} [Fintype ι] (g : ι → ℝ → ℝ) (hg : ∀ i, Integrable (g i)) :
    Integrable (fun x : ι → ℝ => ∏ i, g i (x i)) ∧
      ∫ x : ι → ℝ, ∏ i, g i (x i) = ∏ i, ∫ t, g i t := by
  rw [volume_pi]
  exact ⟨Integrable.fintype_prod hg, integral_fintype_prod_eq_prod _⟩

lemma gB_phi_int : Integrable gB_phi := by simpa using gB_phi_int_pow 0

lemma gB_absphi_int : Integrable (fun x => |x| * gB_phi x) := by
  have := (gB_phi_int_pow 1).norm
  refine this.congr (ae_of_all _ fun x => ?_)
  simp [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gB_phi_nonneg x)]

lemma gB_P_int {ι : Type*} [Fintype ι] : Integrable (gB_P (ι := ι)) ∧ ∫ x, gB_P (ι := ι) x = 1 := by
  have h := gB_int_prod (ι := ι) (fun _ => gB_phi) fun _ => gB_phi_int
  refine ⟨h.1, ?_⟩
  unfold gB_P; rw [h.2]; simp [show ∫ x, gB_phi x = 1 by simpa using gB_m0]

noncomputable def gB_M1 : ℝ := ∫ x, |x| * gB_phi x

lemma gB_M1_val : gB_M1 = 2 * (2 * Real.pi) ^ (-(1 : ℝ) / 2) := by
  unfold gB_M1
  have h := integral_comp_abs (f := fun t => t * ((2 * Real.pi) ^ (-(1 : ℝ) / 2) * Real.exp (-t ^ 2 / 2)))
  have e1 : (fun x => |x| * gB_phi x) =
      fun x => |x| * ((2 * Real.pi) ^ (-(1 : ℝ) / 2) * Real.exp (-|x| ^ 2 / 2)) := by
    funext x; rw [gB_phi_eq, sq_abs]
  rw [e1, h]
  have h2 := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 1) (b := 1 / 2) (by norm_num)
    (by norm_num) (by norm_num)
  have e2 : ∫ x in Set.Ioi (0 : ℝ), x * ((2 * Real.pi) ^ (-(1 : ℝ) / 2) * Real.exp (-x ^ 2 / 2)) =
      (2 * Real.pi) ^ (-(1 : ℝ) / 2) * ∫ x in Set.Ioi (0 : ℝ), x ^ (1 : ℝ) * Real.exp (-(1 / 2) * x ^ (2 : ℝ)) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    simp only [Real.rpow_one, Real.rpow_two]
    ring_nf
  rw [e2, h2]
  norm_num

lemma gB_M1_sq : gB_M1 ^ 2 = 2 / Real.pi := by
  have h : ((2 * Real.pi) ^ (-(1:ℝ) / 2)) ^ 2 = (2 * Real.pi)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num [Real.rpow_neg_one]
  rw [gB_M1_val, mul_pow, h]
  field_simp

lemma gB_M1_nonneg : 0 ≤ gB_M1 :=
  integral_nonneg fun x => mul_nonneg (abs_nonneg x) (gB_phi_nonneg x)

/-- integral of |x_{i0}| against the product density -/
lemma gB_abs_coord {ι : Type*} [Fintype ι] [DecidableEq ι] (i0 : ι) :
    Integrable (fun x : ι → ℝ => |x i0| * gB_P x) ∧
      ∫ x : ι → ℝ, |x i0| * gB_P x = gB_M1 := by
  let g : ι → ℝ → ℝ := fun i t => (if i = i0 then |t| else 1) * gB_phi t
  have hfun : (fun x : ι → ℝ => |x i0| * gB_P x) = fun x => ∏ i, g i (x i) := by
    funext x
    simp only [g, Finset.prod_mul_distrib, gB_P, Finset.prod_ite_eq', Finset.mem_univ, if_true]
  have hg : ∀ i, Integrable (g i) := by
    intro i
    by_cases h : i = i0
    · simp only [g, if_pos h]; exact gB_absphi_int
    · simp only [g, if_neg h, one_mul]; exact gB_phi_int
  have h := gB_int_prod g hg
  rw [hfun]
  refine ⟨h.1, ?_⟩
  rw [h.2, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i0), Finset.prod_eq_one]
  · simp only [g, if_true, mul_one]; rfl
  · intro i hi
    simp only [g, if_neg (Finset.ne_of_mem_erase hi), one_mul]
    simpa using gB_m0

/-- Householder: a reflection sending `c` to `‖c‖ e_{i0}` -/
lemma gB_householder {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℝ) (i0 : ι) :
    ∃ H : Matrix ι ι ℝ, Hᵀ * H = 1 ∧
      ∀ x, c ⬝ᵥ (H *ᵥ x) = Real.sqrt (c ⬝ᵥ c) * x i0 := by
  set r := Real.sqrt (c ⬝ᵥ c) with hr
  have hrr : r * r = c ⬝ᵥ c := Real.mul_self_sqrt (Finset.sum_nonneg fun i _ => mul_self_nonneg (c i))
  set v := c - Pi.single i0 r with hv
  have hvc : v ⬝ᵥ c = r * r - r * c i0 := by
    rw [hv, sub_dotProduct, single_dotProduct, hrr]
  have hvv : v ⬝ᵥ v = 2 * (r * r - r * c i0) := by
    rw [hv, sub_dotProduct, dotProduct_sub, dotProduct_sub, single_dotProduct, dotProduct_single,
      single_dotProduct, hrr]
    simp only [Pi.single_eq_same]; linear_combination hrr
  by_cases h0 : v ⬝ᵥ v = 0
  · refine ⟨1, by simp, fun x => ?_⟩
    have hv0 : v = 0 := dotProduct_self_eq_zero.mp h0
    have hc : c = Pi.single i0 r := by rw [hv, sub_eq_zero] at hv0; exact hv0
    rw [one_mulVec, hc, single_dotProduct]
  · set s := v ⬝ᵥ v
    let H : Matrix ι ι ℝ := 1 - (2 / s) • vecMulVec v v
    have hHx : ∀ x, H *ᵥ x = x - (2 / s * (v ⬝ᵥ x)) • v := by
      intro x
      simp only [H, sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec]
      congr 1
      rw [op_smul_eq_smul, smul_smul]
    have hHT : Hᵀ = H := by
      simp only [H, transpose_sub, transpose_one, transpose_smul, transpose_vecMulVec]
    refine ⟨H, ?_, fun x => ?_⟩
    · rw [hHT, ext_iff_mulVec]
      intro x
      rw [← mulVec_mulVec, hHx, hHx, one_mulVec]
      have : v ⬝ᵥ (x - (2 / s * (v ⬝ᵥ x)) • v) = -(v ⬝ᵥ x) := by
        rw [dotProduct_sub, dotProduct_smul, smul_eq_mul]
        change v ⬝ᵥ x - 2 / s * (v ⬝ᵥ x) * s = _
        field_simp; ring
      rw [this]
      ext i
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    · rw [hHx, dotProduct_sub, dotProduct_smul, smul_eq_mul, dotProduct_comm c v, hvc]
      have hs : s = 2 * (r * r - r * c i0) := hvv
      have hne : r * r - r * c i0 ≠ 0 := by intro h; apply h0; rw [hvv, h, mul_zero]
      have : 2 / s * (v ⬝ᵥ x) * (r * r - r * c i0) = v ⬝ᵥ x := by
        have hne' : r * (r - c i0) ≠ 0 := by
          intro h; apply hne; linear_combination h
        rw [hs]; field_simp
        exact mul_div_cancel_left₀ _ hne'
      rw [this, hv, sub_dotProduct, single_dotProduct]
      ring

lemma gB_C3 {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℝ) (i0 : ι) :
    ∫ x : ι → ℝ, |c ⬝ᵥ x| * gB_P x = gB_M1 * Real.sqrt (c ⬝ᵥ c) := by
  obtain ⟨H, hH, hHc⟩ := gB_householder c i0
  have hF : Continuous fun x : ι → ℝ => |c ⬝ᵥ x| * gB_P x := by
    refine (continuous_abs.comp ?_).mul gB_P_cont
    show Continuous fun x : ι → ℝ => ∑ i, c i * x i
    fun_prop
  rw [← gB_rotG H hH _ hF]
  show ∫ x, |c ⬝ᵥ (H *ᵥ x)| * gB_P (H *ᵥ x) = _
  simp_rw [hHc, gB_P_rot H hH, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), mul_assoc]
  rw [integral_const_mul, (gB_abs_coord i0).2, mul_comm]

lemma gB_sq_int {ι : Type*} [Fintype ι] [DecidableEq ι] (i0 : ι) :
    Integrable (fun x : ι → ℝ => x i0 ^ 2 * gB_P x) ∧ ∫ x : ι → ℝ, x i0 ^ 2 * gB_P x = 1 := by
  let g : ι → ℝ → ℝ := fun i t => (if i = i0 then t ^ 2 else 1) * gB_phi t
  have hfun : (fun x : ι → ℝ => x i0 ^ 2 * gB_P x) = fun x => ∏ i, g i (x i) := by
    funext x
    simp only [g, Finset.prod_mul_distrib, gB_P, Finset.prod_ite_eq', Finset.mem_univ, if_true]
  have hg : ∀ i, Integrable (g i) := by
    intro i
    by_cases h : i = i0
    · simp only [g, if_pos h]; exact gB_phi_int_pow 2
    · simp only [g, if_neg h, one_mul]; exact gB_phi_int
  have h := gB_int_prod g hg
  rw [hfun]
  refine ⟨h.1, ?_⟩
  rw [h.2, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i0), Finset.prod_eq_one]
  · simp only [g, if_true, mul_one]; exact gB_m2
  · intro i hi
    simp only [g, if_neg (Finset.ne_of_mem_erase hi), one_mul]
    simpa using gB_m0

noncomputable def gB_E {k : ℕ} (α : Fin k → ℝ) : ℝ :=
  ∫ x : Fin k → ℝ, |∑ i, α i * x i ^ 2| * gB_P x

lemma gB_E_eq {k : ℕ} (α : Fin k → ℝ) : thetaIntegral k α = gB_E α := by
  unfold thetaIntegral gB_E
  simp_rw [gB_gd]; rfl

lemma gB_E_int {k : ℕ} (α : Fin k → ℝ) :
    Integrable (fun x : Fin k → ℝ => |∑ i, α i * x i ^ 2| * gB_P x) := by
  refine Integrable.mono' (g := fun x => ∑ i, |α i| * (x i ^ 2 * gB_P x))
    (integrable_finset_sum _ fun i _ => (gB_sq_int i).1.const_mul _) ?_ (ae_of_all _ fun x => ?_)
  · refine Continuous.aestronglyMeasurable ?_
    exact (continuous_abs.comp (by fun_prop)).mul gB_P_cont
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gB_P_nonneg x), abs_abs]
    calc |∑ i, α i * x i ^ 2| * gB_P x ≤ (∑ i, |α i * x i ^ 2|) * gB_P x :=
          mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (gB_P_nonneg x)
      _ = _ := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [abs_mul, abs_of_nonneg (sq_nonneg (x i))]; ring

lemma gB_E_nonneg {k : ℕ} (α : Fin k → ℝ) : 0 ≤ gB_E α :=
  integral_nonneg fun x => mul_nonneg (abs_nonneg _) (gB_P_nonneg x)

lemma gB_split {k : ℕ} (f g : (Fin k → ℝ) → ℝ) (hf : Integrable f) (hg : Integrable g) :
    Integrable (fun w : Fin k ⊕ Fin k → ℝ => f (fun i => w (Sum.inl i)) * g (fun i => w (Sum.inr i))) ∧
    ∫ w : Fin k ⊕ Fin k → ℝ, f (fun i => w (Sum.inl i)) * g (fun i => w (Sum.inr i)) =
      (∫ x, f x) * ∫ y, g y := by
  let e := MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin k ⊕ Fin k => ℝ)
  have hmp : MeasurePreserving e volume (volume.prod volume) :=
    measurePreserving_sumPiEquivProdPi (fun _ => volume)
  have hcomp : (fun w : Fin k ⊕ Fin k → ℝ => f (fun i => w (Sum.inl i)) * g (fun i => w (Sum.inr i)))
      = (fun z : (Fin k → ℝ) × (Fin k → ℝ) => f z.1 * g z.2) ∘ e := rfl
  rw [hcomp]
  refine ⟨(hmp.integrable_comp_emb e.measurableEmbedding).mpr (hf.mul_prod hg), ?_⟩
  rw [Function.comp_def, hmp.integral_comp' (fun z : (Fin k → ℝ) × (Fin k → ℝ) => f z.1 * g z.2)]
  exact integral_prod_mul f g

lemma gB_P_sum {k : ℕ} (w : Fin k ⊕ Fin k → ℝ) :
    gB_P w = gB_P (fun i => w (Sum.inl i)) * gB_P (fun i => w (Sum.inr i)) := by
  unfold gB_P; rw [Fintype.prod_sum_type]

/-- the 45-degree rotation on pairs -/
noncomputable def gB_R (k : ℕ) : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) ℝ :=
  fromBlocks (Real.sqrt (1 / 2) • 1) (Real.sqrt (1 / 2) • 1) (Real.sqrt (1 / 2) • 1)
    (-(Real.sqrt (1 / 2)) • 1)

lemma gB_R_orth (k : ℕ) : (gB_R k)ᵀ * gB_R k = 1 := by
  have hc : Real.sqrt (1 / 2) * Real.sqrt (1 / 2) = 1 / 2 := Real.mul_self_sqrt (by norm_num)
  unfold gB_R
  rw [fromBlocks_transpose, fromBlocks_multiply, ← fromBlocks_one]
  simp only [transpose_smul, transpose_one, smul_mul_smul_comm, Matrix.one_mul, neg_mul, mul_neg,
    neg_neg, hc]
  congr 1 <;> rw [← add_smul] <;> norm_num

lemma gB_R_apply (k : ℕ) (w : Fin k ⊕ Fin k → ℝ) (i : Fin k) :
    (gB_R k *ᵥ w) (Sum.inl i) * (gB_R k *ᵥ w) (Sum.inr i) =
      (w (Sum.inl i) ^ 2 - w (Sum.inr i) ^ 2) / 2 := by
  have hc : Real.sqrt (1 / 2) * Real.sqrt (1 / 2) = 1 / 2 := Real.mul_self_sqrt (by norm_num)
  unfold gB_R
  rw [fromBlocks_mulVec]
  simp only [Sum.elim_inl, Sum.elim_inr, Pi.add_apply, smul_mulVec, one_mulVec, Pi.smul_apply,
    smul_eq_mul, Function.comp_apply]
  linear_combination (w (Sum.inl i) ^ 2 - w (Sum.inr i) ^ 2) * hc

lemma gB_cs {k : ℕ} (c : Fin k → ℝ) :
    ∑ i, |c i| ≤ Real.sqrt k * Real.sqrt (c ⬝ᵥ c) := by
  rw [← Real.sqrt_mul (Nat.cast_nonneg k)]
  apply Real.le_sqrt_of_sq_le
  have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => (1 : ℝ)) (fun i => |c i|)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, sq_abs] at this
  simpa [dotProduct, pow_two] using this

noncomputable def gB_D {k : ℕ} (α : Fin k → ℝ) : ℝ :=
  ∫ w : Fin k ⊕ Fin k → ℝ, |∑ i, α i * (w (Sum.inl i) * w (Sum.inr i))| * gB_P w

lemma gB_D_le {k : ℕ} (α : Fin k → ℝ) : gB_D α ≤ gB_E α := by
  have hF : Continuous fun w : Fin k ⊕ Fin k → ℝ =>
      |∑ i, α i * (w (Sum.inl i) * w (Sum.inr i))| * gB_P w :=
    (continuous_abs.comp (by fun_prop)).mul gB_P_cont
  unfold gB_D
  rw [← gB_rotG _ (gB_R_orth k) _ hF]
  simp only [gB_P_rot _ (gB_R_orth k), gB_R_apply]
  have h1 := gB_split (fun x => |∑ i, α i * x i ^ 2| * gB_P x) gB_P (gB_E_int α)
    gB_P_int.1
  have h2 := gB_split gB_P (fun x => |∑ i, α i * x i ^ 2| * gB_P x) gB_P_int.1
    (gB_E_int α)
  have hint := (h1.1.add h2.1).const_mul (1 / 2 : ℝ)
  refine (integral_mono_of_nonneg (ae_of_all _ fun w => mul_nonneg (abs_nonneg _)
    (gB_P_nonneg w)) hint (ae_of_all _ fun w => ?_)).trans ?_
  · simp only
    rw [gB_P_sum w]
    have hP1 := gB_P_nonneg (fun i => w (Sum.inl i))
    have hP2 := gB_P_nonneg (fun i => w (Sum.inr i))
    have : |∑ i, α i * ((w (Sum.inl i) ^ 2 - w (Sum.inr i) ^ 2) / 2)| ≤
        1 / 2 * (|∑ i, α i * w (Sum.inl i) ^ 2| + |∑ i, α i * w (Sum.inr i) ^ 2|) := by
      have e : ∑ i, α i * ((w (Sum.inl i) ^ 2 - w (Sum.inr i) ^ 2) / 2) =
          1 / 2 * (∑ i, α i * w (Sum.inl i) ^ 2 - ∑ i, α i * w (Sum.inr i) ^ 2) := by
        rw [← Finset.sum_sub_distrib, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_; ring
      rw [e, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
      exact mul_le_mul_of_nonneg_left (abs_sub _ _) (by norm_num)
    calc |∑ i, α i * ((w (Sum.inl i) ^ 2 - w (Sum.inr i) ^ 2) / 2)| *
          (gB_P (fun i => w (Sum.inl i)) * gB_P (fun i => w (Sum.inr i)))
        ≤ 1 / 2 * (|∑ i, α i * w (Sum.inl i) ^ 2| + |∑ i, α i * w (Sum.inr i) ^ 2|) *
          (gB_P (fun i => w (Sum.inl i)) * gB_P (fun i => w (Sum.inr i))) :=
          mul_le_mul_of_nonneg_right this (mul_nonneg hP1 hP2)
      _ = _ := by simp only [Pi.add_apply]; ring
  · have hadd := integral_add h1.1 h2.1
    rw [integral_const_mul]
    simp only [Pi.add_apply] at hadd ⊢
    rw [hadd, h1.2, h2.2, gB_P_int.2]
    unfold gB_E; apply le_of_eq; ring

lemma gB_D_ge {k : ℕ} (hk : 1 ≤ k) (α : Fin k → ℝ) :
    gB_M1 ^ 2 * (∑ i, |α i|) / Real.sqrt k ≤ gB_D α := by
  have i0 : Fin k := ⟨0, hk⟩
  let G : (Fin k → ℝ) × (Fin k → ℝ) → ℝ := fun z =>
    |∑ i, α i * (z.1 i * z.2 i)| * (gB_P z.1 * gB_P z.2)
  let e := MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin k ⊕ Fin k => ℝ)
  have hmp : MeasurePreserving e volume (volume.prod volume) :=
    measurePreserving_sumPiEquivProdPi (fun _ => volume)
  have hD : gB_D α = ∫ z, G z ∂(volume.prod volume) := by
    unfold gB_D
    rw [← hmp.integral_comp' G]
    congr 1; funext w
    simp only [G, gB_P_sum w]; rfl
  have hGc : Continuous G := by
    refine (continuous_abs.comp ?_).mul ((gB_P_cont.comp continuous_fst).mul
      (gB_P_cont.comp continuous_snd))
    fun_prop
  have hGint : Integrable G (volume.prod volume) := by
    refine Integrable.mono' (g := fun z => ∑ i, |α i| * ((|z.1 i| * gB_P z.1) *
      (|z.2 i| * gB_P z.2))) (integrable_finset_sum _ fun i _ =>
        (((gB_abs_coord i).1.mul_prod (gB_abs_coord i).1)).const_mul _)
      hGc.aestronglyMeasurable (ae_of_all _ fun z => ?_)
    have hP1 := gB_P_nonneg z.1
    have hP2 := gB_P_nonneg z.2
    simp only [G, Real.norm_eq_abs, abs_mul, abs_abs, abs_of_nonneg hP1, abs_of_nonneg hP2]
    calc |∑ i, α i * (z.1 i * z.2 i)| * (gB_P z.1 * gB_P z.2)
        ≤ (∑ i, |α i * (z.1 i * z.2 i)|) * (gB_P z.1 * gB_P z.2) :=
          mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (mul_nonneg hP1 hP2)
      _ = _ := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [abs_mul, abs_mul]; ring
  have hinner : ∀ x : Fin k → ℝ, ∫ y, G (x, y) =
      gB_P x * (gB_M1 * Real.sqrt ((fun i => α i * x i) ⬝ᵥ (fun i => α i * x i))) := by
    intro x
    rw [← gB_C3 (fun i => α i * x i) i0, ← integral_const_mul]
    congr 1; funext y
    simp only [G, dotProduct]
    rw [show ∑ i, α i * (x i * y i) = ∑ i, α i * x i * y i from
      Finset.sum_congr rfl fun i _ => by ring]
    ring
  have hli := hGint.integral_prod_left
  simp only [hinner] at hli
  rw [hD, integral_prod G hGint]
  simp only [hinner]
  have hsk : 0 < Real.sqrt k := Real.sqrt_pos.mpr (by exact_mod_cast hk)
  have hlow : ∀ x : Fin k → ℝ, gB_M1 / Real.sqrt k * ∑ i, |α i| * (|x i| * gB_P x) ≤
      gB_P x * (gB_M1 * Real.sqrt ((fun i => α i * x i) ⬝ᵥ (fun i => α i * x i))) := by
    intro x
    have hcs := gB_cs (fun i => α i * x i)
    have hP := gB_P_nonneg x
    have hM := gB_M1_nonneg
    have e : ∑ i, |α i| * (|x i| * gB_P x) = (∑ i, |α i * x i|) * gB_P x := by
      rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun i _ => ?_; rw [abs_mul]; ring
    rw [e, div_mul_eq_mul_div, div_le_iff₀ hsk]
    calc gB_M1 * ((∑ i, |α i * x i|) * gB_P x)
        ≤ gB_M1 * ((Real.sqrt k * Real.sqrt ((fun i => α i * x i) ⬝ᵥ (fun i => α i * x i)))
          * gB_P x) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcs hP) hM
      _ = _ := by ring
  have hlint : Integrable fun x : Fin k → ℝ =>
      gB_M1 / Real.sqrt k * ∑ i, |α i| * (|x i| * gB_P x) :=
    (integrable_finset_sum _ fun i _ => (gB_abs_coord i).1.const_mul _).const_mul _
  refine le_trans (le_of_eq ?_) (integral_mono hlint hli hlow)
  rw [integral_const_mul, integral_finset_sum _ fun i _ => (gB_abs_coord i).1.const_mul _]
  simp_rw [integral_const_mul, (gB_abs_coord _).2]
  rw [← Finset.sum_mul]
  ring

lemma gB_E_ge {k : ℕ} (hk : 1 ≤ k) (α : Fin k → ℝ) (hα : ∑ i, |α i| = 1) :
    2 / (Real.pi * Real.sqrt k) ≤ gB_E α := by
  have := (gB_D_ge hk α).trans (gB_D_le α)
  rw [hα, gB_M1_sq, mul_one, div_div] at this
  exact this

/-! ## New lemmas -/

lemma gB_S_bdd (k : ℕ) : BddBelow (thetaIntegral k '' {α : Fin k → ℝ | ∑ i, |α i| = 1}) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨β, _, rfl⟩
  exact integral_nonneg fun u => mul_nonneg (abs_nonneg _) (by unfold gaussDensity; positivity)

lemma gB_S_ne (k : ℕ) (hk : 1 ≤ k) :
    (thetaIntegral k '' {α : Fin k → ℝ | ∑ i, |α i| = 1}).Nonempty :=
  ⟨_, ⟨Pi.single ⟨0, hk⟩ 1, by
      show ∑ i, |Pi.single (⟨0, hk⟩ : Fin k) (1 : ℝ) i| = 1
      rw [Fintype.sum_eq_single ⟨0, hk⟩ (fun j hj => by simp [Pi.single_apply, hj])]; simp, rfl⟩⟩

lemma gB_s_pos (k : ℕ) (hk : 1 ≤ k) :
    0 < sInf (thetaIntegral k '' {α : Fin k → ℝ | ∑ i, |α i| = 1}) := by
  have hsk : 0 < Real.sqrt k := Real.sqrt_pos.mpr (by exact_mod_cast hk)
  have hL : 0 < 2 / (Real.pi * Real.sqrt k) := by positivity
  refine lt_of_lt_of_le hL (le_csInf (gB_S_ne k hk) ?_)
  rintro _ ⟨α, hα, rfl⟩
  rw [gB_E_eq]; exact gB_E_ge hk α hα

lemma gB_snoc (k : ℕ) (α : Fin k → ℝ) :
    thetaIntegral (k + 1) (Fin.snoc α 0) = thetaIntegral k α := by
  rw [gB_E_eq, gB_E_eq]
  unfold gB_E
  have hmp := volume_preserving_piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) (Fin.last k)
  let F : ℝ × (Fin k → ℝ) → ℝ := fun p => gB_phi p.1 * (|∑ i, α i * p.2 i ^ 2| * gB_P p.2)
  have hpt : ∀ x : Fin (k + 1) → ℝ,
      |∑ i, (Fin.snoc α 0 : Fin (k + 1) → ℝ) i * x i ^ 2| * gB_P x =
        F (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) (Fin.last k) x) := by
    intro x
    simp only [F, gB_P, MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv,
      Fin.sum_univ_castSucc, Fin.prod_univ_castSucc]
    simp only [Equiv.coe_fn_symm_mk, Fin.removeNth, Fin.succAbove_last, Fin.snoc_castSucc,
      Fin.snoc_last, zero_mul, add_zero]
    ring
  calc ∫ x : Fin (k + 1) → ℝ, |∑ i, (Fin.snoc α 0 : Fin (k + 1) → ℝ) i * x i ^ 2| * gB_P x
      = ∫ x, F (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) (Fin.last k) x) := by
        congr 1; funext x; exact hpt x
    _ = ∫ p, F p := hmp.integral_comp' F
    _ = (∫ t, gB_phi t) * ∫ y : Fin k → ℝ, |∑ i, α i * y i ^ 2| * gB_P y := by
        rw [Measure.volume_eq_prod]; exact integral_prod_mul (fun t => gB_phi t) (fun y : Fin k → ℝ => |∑ i, α i * y i ^ 2| * gB_P y)
    _ = _ := by
        have hφ : ∫ t, gB_phi t = 1 := by simpa using gB_m0
        rw [hφ, one_mul]

lemma gB_s_succ (k : ℕ) (hk : 1 ≤ k) :
    sInf (thetaIntegral (k + 1) '' {α : Fin (k + 1) → ℝ | ∑ i, |α i| = 1}) ≤
      sInf (thetaIntegral k '' {α : Fin k → ℝ | ∑ i, |α i| = 1}) := by
  refine le_csInf (gB_S_ne k hk) ?_
  rintro _ ⟨α, hα, rfl⟩
  rw [← gB_snoc]
  refine csInf_le (gB_S_bdd _) ⟨_, ?_, rfl⟩
  show ∑ i, |(Fin.snoc α 0 : Fin (k + 1) → ℝ) i| = 1
  rw [Fin.sum_univ_castSucc]
  simpa using hα

lemma gB_s_mono (r μ : ℕ) (hr : 1 ≤ r) (h : r ≤ μ) :
    sInf (thetaIntegral μ '' {α : Fin μ → ℝ | ∑ i, |α i| = 1}) ≤
      sInf (thetaIntegral r '' {α : Fin r → ℝ | ∑ i, |α i| = 1}) := by
  induction μ, h using Nat.le_induction with
  | base => exact le_rfl
  | succ m hm ih => exact (gB_s_succ m (hr.trans hm)).trans ih

theorem theta_pos (k : ℕ) (hk : 1 ≤ k) : 0 < theta k := by
  have := gB_s_pos k hk
  unfold theta; positivity

theorem theta_mono {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) : theta a ≤ theta b := by
  unfold theta
  exact one_div_le_one_div_of_le (gB_s_pos b (ha.trans hab)) (gB_s_mono a b ha hab)

theorem theta_nonneg (k : ℕ) : 0 ≤ theta k := by
  unfold theta
  refine one_div_nonneg.mpr (Real.sInf_nonneg ?_)
  rintro _ ⟨β, _, rfl⟩
  exact integral_nonneg fun u => mul_nonneg (abs_nonneg _) (by unfold gaussDensity; positivity)

theorem gauss_le {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsHermitian) (μ : ℕ)
    (hμ : B.rank ≤ μ) :
    eigL1 B ≤ theta μ * ∫ u : Fin n → ℝ, |u ⬝ᵥ (B *ᵥ u)| * gaussDensity n u := by
  have hI0 : 0 ≤ ∫ u : Fin n → ℝ, |u ⬝ᵥ (B *ᵥ u)| * gaussDensity n u :=
    integral_nonneg fun u => mul_nonneg (abs_nonneg _) (by unfold gaussDensity; positivity)
  rcases Nat.eq_zero_or_pos B.rank with h0 | hpos
  · have : eigL1 B = 0 := by
      have hc := hB.rank_eq_card_non_zero_eigs
      rw [h0, eq_comm, Fintype.card_eq_zero_iff] at hc
      unfold eigL1 eigVec
      rw [dif_pos hB]
      refine Finset.sum_eq_zero fun i _ => ?_
      by_contra hne
      exact hc.false ⟨i, fun h => hne (by rw [h, abs_zero])⟩
    rw [this]; exact mul_nonneg (theta_nonneg μ) hI0
  · have hg := (gaussian_quadratic_form B hB).2
    have hsr := gB_s_pos _ hpos
    have hsμ := gB_s_pos μ (hpos.trans_le hμ)
    have hmono := gB_s_mono _ μ hpos hμ
    have hth : theta B.rank ≤ theta μ := by
      unfold theta; exact one_div_le_one_div_of_le hsμ hmono
    have hthpos : 0 < theta B.rank := by unfold theta; positivity
    have : eigL1 B ≤ theta B.rank * ∫ u : Fin n → ℝ, |u ⬝ᵥ (B *ᵥ u)| * gaussDensity n u := by
      rw [ge_iff_le, one_div, inv_mul_le_iff₀ hthpos] at hg
      exact hg
    exact this.trans (mul_le_mul_of_nonneg_right hth hI0)

theorem integrable_quad {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) :
    Integrable (fun u : Fin n → ℝ => (u ⬝ᵥ (B *ᵥ u)) * gaussDensity n u) := by
  have : (fun u : Fin n → ℝ => (u ⬝ᵥ (B *ᵥ u)) * gaussDensity n u) =
      fun u => ∑ i, ∑ j, B i j * (u i * u j * gaussDensity n u) := by
    funext u
    simp only [dotProduct, mulVec, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [this]
  exact integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ =>
    (gB_pair i j).1.const_mul _

end MC99


open Matrix MeasureTheory
open ModernConvex.MatrixCube

namespace MC99

section sepA_section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-- Local convexity of the matrix space (with the local normed structure). -/
theorem sepA_lcs {n : ℕ} : LocallyConvexSpace ℝ (Matrix (Fin n) (Fin n) ℝ) :=
  NormedSpace.toLocallyConvexSpace

attribute [local instance] sepA_lcs

lemma sepA_spec {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsHermitian) :
    ∃ U : Matrix (Fin n) (Fin n) ℝ, Uᵀ * U = 1 ∧ U * Uᵀ = 1 ∧
      M = U * diagonal hM.eigenvalues * Uᵀ := by
  refine ⟨(hM.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ), ?_, ?_, ?_⟩
  · have := Unitary.coe_star_mul_self hM.eigenvectorUnitary
    simpa [Matrix.star_eq_conjTranspose] using this
  · have := Unitary.coe_mul_star_self hM.eigenvectorUnitary
    simpa [Matrix.star_eq_conjTranspose] using this
  · conv_lhs => rw [hM.spectral_theorem]
    simp [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]

lemma sepA_psd_conj {n : ℕ} (U : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ)
    (hd : ∀ k, 0 ≤ d k) : (U * diagonal d * Uᵀ).PosSemidef := by
  have := (PosSemidef.diagonal (fun k => hd k)).mul_mul_conjTranspose_same U
  simpa [conjTranspose_eq_transpose_of_trivial] using this

lemma sepA_abs {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsHermitian) :
    ∃ Q : Matrix (Fin n) (Fin n) ℝ, (Q - B).PosSemidef ∧ (Q + B).PosSemidef ∧
      Q.trace = eigL1 B := by
  obtain ⟨U, h1, h2, hBU⟩ := sepA_spec B hB
  have hE : eigL1 B = ∑ k, |hB.eigenvalues k| := by
    unfold eigL1 eigVec; rw [dif_pos hB]
  rw [hE]
  generalize hB.eigenvalues = l at hBU ⊢
  refine ⟨U * diagonal (fun k => |l k|) * Uᵀ, ?_, ?_, ?_⟩
  · have : U * diagonal (fun k => |l k|) * Uᵀ - B =
        U * diagonal (fun k => |l k| - l k) * Uᵀ := by
      conv_lhs => rw [hBU]
      rw [← Matrix.sub_mul, ← Matrix.mul_sub, diagonal_sub]
    rw [this]
    exact sepA_psd_conj _ _ (fun k => by have := le_abs_self (l k); linarith)
  · have : U * diagonal (fun k => |l k|) * Uᵀ + B =
        U * diagonal (fun k => |l k| + l k) * Uᵀ := by
      conv_lhs => rw [hBU]
      rw [← Matrix.add_mul, ← Matrix.mul_add, diagonal_add]
    rw [this]
    exact sepA_psd_conj _ _ (fun k => by have := neg_abs_le (l k); linarith)
  · rw [trace_mul_comm, ← Matrix.mul_assoc, h1, Matrix.one_mul, trace_diagonal]

/-- The cone-like set `{∑ Xᵢ + P}`. -/
def sepA_S {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (ρ : ℝ) :
    Set (Matrix (Fin n) (Fin n) ℝ) :=
  {Y | ∃ X : Fin m → Matrix (Fin n) (Fin n) ℝ, ∃ P : Matrix (Fin n) (Fin n) ℝ,
    (∀ i, (X i - ρ • A i).PosSemidef ∧ (X i + ρ • A i).PosSemidef) ∧ P.PosSemidef ∧
      Y = ∑ i, X i + P}

lemma sepA_X_psd {n : ℕ} {X A : Matrix (Fin n) (Fin n) ℝ} {ρ : ℝ}
    (h1 : (X - ρ • A).PosSemidef) (h2 : (X + ρ • A).PosSemidef) : X.PosSemidef := by
  have := (h1.add h2).smul (show (0:ℝ) ≤ 1/2 by norm_num)
  convert this using 1
  ext i j; simp; ring

lemma sepA_mem_psd {n m : ℕ} {A : Fin m → Matrix (Fin n) (Fin n) ℝ} {ρ : ℝ}
    {Y : Matrix (Fin n) (Fin n) ℝ} (hY : Y ∈ sepA_S A ρ) : Y.PosSemidef := by
  obtain ⟨X, P, hX, hP, rfl⟩ := hY
  exact (posSemidef_sum _ fun i _ => sepA_X_psd (hX i).1 (hX i).2).add hP

lemma sepA_add_psd {n m : ℕ} {A : Fin m → Matrix (Fin n) (Fin n) ℝ} {ρ : ℝ}
    {Y V : Matrix (Fin n) (Fin n) ℝ} (hY : Y ∈ sepA_S A ρ) (hV : V.PosSemidef) :
    Y + V ∈ sepA_S A ρ := by
  obtain ⟨X, P, hX, hP, rfl⟩ := hY
  exact ⟨X, P + V, hX, hP.add hV, by rw [add_assoc]⟩

lemma sepA_notmem {n m : ℕ} (A₀ : Matrix (Fin n) (Fin n) ℝ)
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (ρ : ℝ)
    (hS : ¬ SystemSolvable A₀ A ρ) : A₀ ∉ sepA_S A ρ := by
  rintro ⟨X, P, hX, hP, hY⟩
  apply hS
  refine ⟨X, fun i => (sepA_X_psd (hX i).1 (hX i).2).isHermitian,
    fun i => ⟨(hX i).1, by simpa [sub_neg_eq_add, neg_smul] using (hX i).2⟩, ?_⟩
  rw [hY]; simpa using hP

lemma sepA_convex {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (ρ : ℝ) :
    Convex ℝ (sepA_S A ρ) := by
  rintro _ ⟨X, P, hX, hP, rfl⟩ _ ⟨X', P', hX', hP', rfl⟩ a b ha hb hab
  obtain rfl : b = 1 - a := by linarith
  refine ⟨fun i => a • X i + (1 - a) • X' i, a • P + (1 - a) • P', fun i => ⟨?_, ?_⟩,
    (hP.smul ha).add (hP'.smul hb), ?_⟩
  · have := ((hX i).1.smul ha).add ((hX' i).1.smul hb)
    convert this using 1
    ext j k; simp; ring
  · have := ((hX i).2.smul ha).add ((hX' i).2.smul hb)
    convert this using 1
    ext j k; simp; ring
  · ext j k; simp [Matrix.sum_apply, Finset.mul_sum, Finset.sum_add_distrib]; ring

lemma sepA_closed_psd {n : ℕ} : IsClosed {X : Matrix (Fin n) (Fin n) ℝ | X.PosSemidef} := by
  have : {X : Matrix (Fin n) (Fin n) ℝ | X.PosSemidef} =
      {X | Xᴴ = X} ∩ ⋂ x : Fin n → ℝ, {X | 0 ≤ star x ⬝ᵥ (X *ᵥ x)} := by
    ext X; simp [posSemidef_iff_dotProduct_mulVec, IsHermitian]
  rw [this]
  refine IsClosed.inter (isClosed_eq (by fun_prop) continuous_id)
    (isClosed_iInter fun x => isClosed_le continuous_const ?_)
  exact continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)

lemma sepA_entry_le {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.PosSemidef) (j k : Fin n) :
    |X j k| ≤ X.trace := by
  have hdiag : ∀ i, 0 ≤ X i i := fun i => hX.diag_nonneg
  by_cases hjk : j = k
  · subst hjk
    rw [abs_of_nonneg (hdiag j)]
    exact Finset.single_le_sum (f := fun i => X i i) (fun i _ => hdiag i) (Finset.mem_univ j)
  · have hsym : X k j = X j k := by
      have := hX.isHermitian.apply j k; simpa using this
    have key : ∀ s : ℝ, 0 ≤ X j j + (s * X k j + s * (X j k + s * X k k)) := by
      intro s
      have := hX.dotProduct_mulVec_nonneg (Pi.single j 1 + s • Pi.single k 1)
      simpa [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, mulVec_single_one,
        dotProduct_single, single_dotProduct, add_assoc, mul_comm, mul_left_comm] using this
    have h1 := key 1
    have h2 := key (-1)
    have htr : X j j + X k k ≤ X.trace := by
      have := Finset.sum_le_sum_of_subset_of_nonneg (f := fun i => X i i)
        (Finset.subset_univ {j, k}) (fun i _ _ => hdiag i)
      rw [Finset.sum_pair hjk] at this
      exact this
    rw [abs_le]; constructor <;> nlinarith [hdiag j, hdiag k]

lemma sepA_norm_le {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.PosSemidef) :
    ‖X‖ ≤ X.trace := by
  rw [Matrix.norm_le_iff hX.trace_nonneg]
  intro j k
  rw [Real.norm_eq_abs]; exact sepA_entry_le hX j k

/-- Bounded-trace part, as a set of tuples. -/
def sepA_K {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (ρ R : ℝ) :
    Set ((Fin m → Matrix (Fin n) (Fin n) ℝ) × Matrix (Fin n) (Fin n) ℝ) :=
  {p | (∀ i, (p.1 i - ρ • A i).PosSemidef ∧ (p.1 i + ρ • A i).PosSemidef) ∧ p.2.PosSemidef ∧
    (∑ i, p.1 i + p.2).trace ≤ R}

lemma sepA_K_closed {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (ρ R : ℝ) :
    IsClosed (sepA_K A ρ R) := by
  have h1 : ∀ i, IsClosed {p : (Fin m → Matrix (Fin n) (Fin n) ℝ) × Matrix (Fin n) (Fin n) ℝ |
      (p.1 i - ρ • A i).PosSemidef} := fun i =>
    sepA_closed_psd.preimage (by fun_prop)
  have h2 : ∀ i, IsClosed {p : (Fin m → Matrix (Fin n) (Fin n) ℝ) × Matrix (Fin n) (Fin n) ℝ |
      (p.1 i + ρ • A i).PosSemidef} := fun i =>
    sepA_closed_psd.preimage (by fun_prop)
  have h3 : IsClosed {p : (Fin m → Matrix (Fin n) (Fin n) ℝ) × Matrix (Fin n) (Fin n) ℝ |
      p.2.PosSemidef} := sepA_closed_psd.preimage (by fun_prop)
  have h4 : IsClosed {p : (Fin m → Matrix (Fin n) (Fin n) ℝ) × Matrix (Fin n) (Fin n) ℝ |
      (∑ i, p.1 i + p.2).trace ≤ R} :=
    isClosed_le (Continuous.matrix_trace (by fun_prop)) continuous_const
  have : sepA_K A ρ R = (⋂ i, ({p : (Fin m → Matrix (Fin n) (Fin n) ℝ) ×
      Matrix (Fin n) (Fin n) ℝ | (p.1 i - ρ • A i).PosSemidef} ∩
      {p | (p.1 i + ρ • A i).PosSemidef})) ∩
      ({p | p.2.PosSemidef} ∩ {p | (∑ i, p.1 i + p.2).trace ≤ R}) := by
    ext p; simp [sepA_K, forall_and]
  rw [this]
  exact (isClosed_iInter fun i => (h1 i).inter (h2 i)).inter (h3.inter h4)

lemma sepA_K_compact {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (ρ R : ℝ) :
    IsCompact (sepA_K A ρ R) := by
  refine Metric.isCompact_of_isClosed_isBounded (sepA_K_closed A ρ R) ?_
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨R, fun p hp => ?_⟩
  obtain ⟨hX, hP, hR⟩ := hp
  have hXp : ∀ i, (p.1 i).PosSemidef := fun i => sepA_X_psd (hX i).1 (hX i).2
  have htr : (∑ i, p.1 i + p.2).trace = ∑ i, (p.1 i).trace + p.2.trace := by
    rw [trace_add, trace_sum]
  rw [htr] at hR
  have hsum0 : 0 ≤ ∑ i, (p.1 i).trace := Finset.sum_nonneg fun i _ => (hXp i).trace_nonneg
  have hP0 := hP.trace_nonneg
  have hR0 : 0 ≤ R := by linarith
  rw [Metric.mem_closedBall, dist_zero_right, norm_prod_le_iff]
  constructor
  · rw [pi_norm_le_iff_of_nonneg hR0]
    intro i
    have : (p.1 i).trace ≤ ∑ i, (p.1 i).trace :=
      Finset.single_le_sum (f := fun i => (p.1 i).trace) (fun i _ => (hXp i).trace_nonneg)
        (Finset.mem_univ i)
    linarith [sepA_norm_le (hXp i)]
  · linarith [sepA_norm_le hP]

lemma sepA_closed {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (ρ : ℝ) :
    IsClosed (sepA_S A ρ) := by
  refine closure_subset_iff_isClosed.mp fun x hx => ?_
  set R := x.trace + 1
  have hU : IsOpen {Y : Matrix (Fin n) (Fin n) ℝ | Y.trace < R} :=
    isOpen_lt (Continuous.matrix_trace continuous_id) continuous_const
  have hxU : x ∈ {Y : Matrix (Fin n) (Fin n) ℝ | Y.trace < R} := by simp [R]
  have hcomp : IsCompact ((fun p : (Fin m → Matrix (Fin n) (Fin n) ℝ) ×
      Matrix (Fin n) (Fin n) ℝ => ∑ i, p.1 i + p.2) '' sepA_K A ρ R) :=
    (sepA_K_compact A ρ R).image (by fun_prop)
  have h1 : x ∈ closure ({Y : Matrix (Fin n) (Fin n) ℝ | Y.trace < R} ∩ sepA_S A ρ) :=
    hU.inter_closure ⟨hxU, hx⟩
  have h2 : {Y : Matrix (Fin n) (Fin n) ℝ | Y.trace < R} ∩ sepA_S A ρ ⊆
      (fun p : (Fin m → Matrix (Fin n) (Fin n) ℝ) ×
      Matrix (Fin n) (Fin n) ℝ => ∑ i, p.1 i + p.2) '' sepA_K A ρ R := by
    rintro _ ⟨hlt, X, P, hX, hP, rfl⟩
    exact ⟨(X, P), ⟨hX, hP, le_of_lt hlt⟩, rfl⟩
  obtain ⟨p, hp, rfl⟩ := hcomp.isClosed.closure_subset (closure_mono h2 h1)
  exact ⟨p.1, p.2, hp.1, hp.2.1, rfl⟩

lemma sepA_lin {n : ℕ} (f : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ) :
    ∃ W : Matrix (Fin n) (Fin n) ℝ, W.IsHermitian ∧
      ∀ Y : Matrix (Fin n) (Fin n) ℝ, Y.IsHermitian → f Y = (W * Y).trace := by
  classical
  set G : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun j k => f (single j k 1)
  have hG : ∀ Y, f Y = (Gᵀ * Y).trace := by
    intro Y
    conv_lhs => rw [Matrix.matrix_eq_sum_single Y]
    have hs : ∀ j k, single j k (Y j k) = Y j k • single j k (1 : ℝ) := by
      intro j k; rw [smul_single, smul_eq_mul, mul_one]
    simp only [hs, map_sum, map_smul, smul_eq_mul, trace, diag, mul_apply, transpose_apply, G,
      of_apply]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  refine ⟨(1/2 : ℝ) • (G + Gᵀ), ?_, fun Y hY => ?_⟩
  · ext j k; simp; ring
  · have hYt : Yᵀ = Y := by
      have := hY.eq; rwa [conjTranspose_eq_transpose_of_trivial] at this
    have : (G * Y).trace = (Gᵀ * Y).trace := by
      rw [← trace_transpose, transpose_mul, hYt, trace_mul_comm]
    rw [hG, Matrix.smul_mul, trace_smul, Matrix.add_mul, trace_add, this, smul_eq_mul]; ring

lemma sepA_trace_vv {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    (W * vecMulVec v v).trace = star v ⬝ᵥ (W *ᵥ v) := by
  simp only [trace, diag, mul_apply, vecMulVec_apply, dotProduct, mulVec, star_trivial,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem sep {n m : ℕ} (A₀ : Matrix (Fin n) (Fin n) ℝ) (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hA₀ : A₀.PosSemidef) (hA : ∀ i, (A i).IsHermitian) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hS : ¬ SystemSolvable A₀ A ρ) :
    ∃ M : Matrix (Fin n) (Fin n) ℝ,
      (Mᵀ * A₀ * M).trace < ρ * ∑ i, eigL1 (Mᵀ * A i * M) := by
  classical
  have hnot := sepA_notmem A₀ A ρ hS
  obtain ⟨f, u, hfA, hfS⟩ :=
    geometric_hahn_banach_point_closed (sepA_convex A ρ) (sepA_closed A ρ) hnot
  obtain ⟨W, hWh, hW⟩ := sepA_lin (f : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ)
  have hSh : ∀ c ∈ sepA_S A ρ, c.IsHermitian := fun c hc => (sepA_mem_psd hc).isHermitian
  have hWS : ∀ c ∈ sepA_S A ρ, u < (W * c).trace := fun c hc => by
    rw [← hW c (hSh c hc)]; exact hfS c hc
  have hWA : (W * A₀).trace < u := by rw [← hW A₀ hA₀.isHermitian]; exact hfA
  have hS0 : ∀ c ∈ sepA_S A ρ, 0 ≤ c.trace := fun c hc => (sepA_mem_psd hc).trace_nonneg
  -- a member of S
  choose Q hQ1 hQ2 _ using fun i => sepA_abs (A i) (hA i)
  have hc0 : ∑ i, ρ • Q i ∈ sepA_S A ρ := by
    refine ⟨fun i => ρ • Q i, 0, fun i => ⟨?_, ?_⟩, PosSemidef.zero, by simp⟩
    · rw [← smul_sub]; exact (hQ1 i).smul hρ
    · rw [← smul_add]; exact (hQ2 i).smul hρ
  have hWpsd : W.PosSemidef := by
    refine PosSemidef.of_dotProduct_mulVec_nonneg hWh fun v => ?_
    by_contra hneg
    push Not at hneg
    set q := star v ⬝ᵥ (W *ᵥ v) with hq
    set c0 := ∑ i, ρ • Q i
    have hV : (vecMulVec v v).PosSemidef := by
      simpa using posSemidef_vecMulVec_self_star v
    set t : ℝ := ((W * c0).trace - u) / (-q) + 1 with ht_def
    have ht : 0 ≤ t := by
      have : 0 ≤ ((W * c0).trace - u) / (-q) :=
        div_nonneg (by linarith [hWS c0 hc0]) (by linarith)
      linarith
    have hmem := sepA_add_psd hc0 (hV.smul ht)
    have h := hWS _ hmem
    rw [Matrix.mul_add, trace_add, Matrix.mul_smul, trace_smul, sepA_trace_vv, smul_eq_mul] at h
    have e : t * q = u - (W * c0).trace + q := by
      have hq0 : q ≠ 0 := hneg.ne
      rw [ht_def]; field_simp; ring
    rw [← hq] at h
    linarith
  set δ := u - (W * A₀).trace
  have hδ : 0 < δ := by simp only [δ]; linarith
  have htA := hA₀.trace_nonneg
  set ε := δ / (A₀.trace + 1)
  have hε : 0 < ε := div_pos hδ (by linarith)
  have hεA : ε * A₀.trace < δ := by
    have : ε * (A₀.trace + 1) = δ := div_mul_cancel₀ _ (by linarith)
    nlinarith
  -- spectral decomposition of W
  obtain ⟨U, h1, h2, hWU⟩ := sepA_spec W hWh
  have hl : ∀ k, 0 ≤ hWh.eigenvalues k := hWpsd.eigenvalues_nonneg
  generalize hWh.eigenvalues = l at hWU hl
  set d : Fin n → ℝ := fun k => l k + ε with hd_def
  have hd : ∀ k, 0 < d k := fun k => by simp only [d]; linarith [hl k]
  set M := U * diagonal (fun k => Real.sqrt (d k)) with hM_def
  set N := diagonal (fun k => 1 / Real.sqrt (d k)) * Uᵀ with hN_def
  have hsq : ∀ k, Real.sqrt (d k) * Real.sqrt (d k) = d k :=
    fun k => Real.mul_self_sqrt (hd k).le
  have hsq0 : ∀ k, Real.sqrt (d k) ≠ 0 := fun k => (Real.sqrt_pos.2 (hd k)).ne'
  have hNM : N * M = 1 := by
    rw [hN_def, hM_def, Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ, h1, Matrix.one_mul,
      diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext k; field_simp [hsq0 k]
  have hMN : M * N = 1 := by
    rw [hN_def, hM_def, Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal _) (diagonal _),
      diagonal_mul_diagonal]
    have : (diagonal fun k => Real.sqrt (d k) * (1 / Real.sqrt (d k))) = 1 := by
      rw [← diagonal_one]; congr 1; funext k; field_simp [hsq0 k]
    rw [this, Matrix.one_mul, h2]
  have hMM : M * Mᵀ = U * diagonal d * Uᵀ := by
    rw [hM_def, transpose_mul, diagonal_transpose, Matrix.mul_assoc,
      ← Matrix.mul_assoc (diagonal _) (diagonal _), diagonal_mul_diagonal, ← Matrix.mul_assoc]
    congr 3; funext k; exact hsq k
  have hdiag : diagonal d = diagonal l + ε • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j; by_cases hij : i = j
    · subst hij; simp [d]
    · simp [hij, one_apply]
  have hWε : W + ε • (1 : Matrix (Fin n) (Fin n) ℝ) = M * Mᵀ := by
    rw [hMM, hdiag, Matrix.mul_add, Matrix.add_mul, ← hWU, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, h2]
  have hB : ∀ i, (Mᵀ * A i * M).IsHermitian := fun i => by
    simpa [conjTranspose_eq_transpose_of_trivial] using isHermitian_conjTranspose_mul_mul M (hA i)
  choose R hR1 hR2 hR3 using fun i => sepA_abs _ (hB i)
  have hNB : ∀ i, Nᵀ * (Mᵀ * A i * M) * N = A i := by
    intro i
    calc Nᵀ * (Mᵀ * A i * M) * N = (M * N)ᵀ * A i * (M * N) := by
          simp only [transpose_mul, Matrix.mul_assoc]
      _ = A i := by rw [hMN]; simp
  set c := ∑ i, ρ • (Nᵀ * R i * N) with hc_def
  have hc : c ∈ sepA_S A ρ := by
    refine ⟨fun i => ρ • (Nᵀ * R i * N), 0, fun i => ⟨?_, ?_⟩, PosSemidef.zero, by simp [c]⟩
    · have := ((hR1 i).conjTranspose_mul_mul_same N).smul hρ
      rw [conjTranspose_eq_transpose_of_trivial, Matrix.mul_sub, Matrix.sub_mul, hNB,
        smul_sub] at this
      exact this
    · have := ((hR2 i).conjTranspose_mul_mul_same N).smul hρ
      rw [conjTranspose_eq_transpose_of_trivial, Matrix.mul_add, Matrix.add_mul, hNB,
        smul_add] at this
      exact this
  have htc : ((W + ε • (1 : Matrix (Fin n) (Fin n) ℝ)) * c).trace =
      ρ * ∑ i, eigL1 (Mᵀ * A i * M) := by
    rw [hWε, hc_def, Matrix.mul_sum, trace_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mul_smul, trace_smul, smul_eq_mul, ← hR3 i]
    congr 1
    calc (M * Mᵀ * (Nᵀ * R i * N)).trace = (M * (N * M)ᵀ * R i * N).trace := by
          simp only [transpose_mul, Matrix.mul_assoc]
      _ = (R i).trace := by
          rw [hNM, transpose_one, Matrix.mul_one, trace_mul_comm, ← Matrix.mul_assoc, hNM,
            Matrix.one_mul]
  have htA' : ((W + ε • (1 : Matrix (Fin n) (Fin n) ℝ)) * A₀).trace = (Mᵀ * A₀ * M).trace := by
    rw [hWε, Matrix.mul_assoc, trace_mul_comm]
  refine ⟨M, ?_⟩
  rw [← htA', ← htc]
  have e : ∀ Y : Matrix (Fin n) (Fin n) ℝ,
      ((W + ε • (1 : Matrix (Fin n) (Fin n) ℝ)) * Y).trace = (W * Y).trace + ε * Y.trace := by
    intro Y
    rw [Matrix.add_mul, trace_add, Matrix.smul_mul, Matrix.one_mul, trace_smul, smul_eq_mul]
  rw [e, e]
  have h1 := hWS c hc
  have h2 : 0 ≤ ε * c.trace := mul_nonneg hε.le (hS0 c hc)
  simp only [δ] at hεA
  linarith

end sepA_section

end MC99


open Matrix MeasureTheory
open ModernConvex.MatrixCube

namespace MC99

lemma mn_gd_nonneg (k : ℕ) (u : Fin k → ℝ) : 0 ≤ gaussDensity k u := by
  unfold gaussDensity; positivity

lemma mn_int_abs {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) :
    Integrable (fun u : Fin n → ℝ => |u ⬝ᵥ (B *ᵥ u)| * gaussDensity n u) := by
  refine (integrable_quad B).abs.congr (Filter.Eventually.of_forall fun u => ?_)
  simp only [abs_mul, abs_of_nonneg (mn_gd_nonneg n u)]

lemma mn_quad {n : ℕ} (C M : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) :
    (M *ᵥ u) ⬝ᵥ (C *ᵥ (M *ᵥ u)) = u ⬝ᵥ ((Mᵀ * C * M) *ᵥ u) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec u Mᵀ,
    Matrix.vecMul_transpose]

end MC99


section D1

open Matrix MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator
open ModernConvex.MatrixCube

namespace MX

/-- Euclidean norm of a vector. -/
noncomputable def nrm {k : ℕ} (v : Fin k → ℝ) : ℝ := Real.sqrt (∑ i, v i ^ 2)

/-- Frobenius norm of a matrix. -/
noncomputable def fro {a b : ℕ} (X : Matrix (Fin a) (Fin b) ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, X i j ^ 2)

lemma nrm_sq {k : ℕ} (v : Fin k → ℝ) : nrm v ^ 2 = v ⬝ᵥ v := by
  rw [nrm, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  simp [dotProduct, sq]

lemma nrm_nonneg {k : ℕ} (v : Fin k → ℝ) : 0 ≤ nrm v := Real.sqrt_nonneg _

lemma opnorm_vecMulVec {p q : ℕ} (a : Fin p → ℝ) (b : Fin q → ℝ) :
    ‖vecMulVec a b‖ ≤ nrm a * nrm b := by
  rw [l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (nrm_nonneg _) (nrm_nonneg _))
    fun x => ?_
  have hx : ‖x‖ = nrm (WithLp.ofLp x) := by
    rw [EuclideanSpace.norm_eq, nrm]; simp [Real.norm_eq_abs, sq_abs]
  have hv : ((toEuclideanLin (𝕜 := ℝ) (m := Fin p) (n := Fin q)).trans
      LinearMap.toContinuousLinearMap (vecMulVec a b)) x =
      WithLp.toLp 2 ((b ⬝ᵥ WithLp.ofLp x) • a) := by
    ext i
    simp [toEuclideanLin, vecMulVec_mulVec, mul_comm]
  rw [hv, EuclideanSpace.norm_eq, hx]
  have h1 : Real.sqrt (∑ i, ‖((b ⬝ᵥ WithLp.ofLp x) • a) i‖ ^ 2) =
      |b ⬝ᵥ WithLp.ofLp x| * nrm a := by
    rw [nrm, ← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg _)]
    congr 1
    simp [Real.norm_eq_abs, sq_abs, mul_pow, Finset.mul_sum]
  rw [h1]
  have hcs : |b ⬝ᵥ WithLp.ofLp x| ≤ nrm b * nrm (WithLp.ofLp x) := by
    rw [← Real.sqrt_sq_eq_abs, nrm, nrm, ← Real.sqrt_mul (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    apply Real.sqrt_le_sqrt
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ b (WithLp.ofLp x)
    simpa [dotProduct] using this
  calc |b ⬝ᵥ WithLp.ofLp x| * nrm a ≤ nrm b * nrm (WithLp.ofLp x) * nrm a :=
        mul_le_mul_of_nonneg_right hcs (nrm_nonneg _)
    _ = nrm a * nrm b * nrm (WithLp.ofLp x) := by ring

theorem opsq {p q : ℕ} (Z : Matrix (Fin p) (Fin q) ℝ) (hZ : ‖Z‖ ≤ 1) (b : Fin q → ℝ) :
    (Z *ᵥ b) ⬝ᵥ (Z *ᵥ b) ≤ b ⬝ᵥ b := by
  have h := Matrix.l2_opNorm_mulVec Z ((EuclideanSpace.equiv (Fin q) ℝ).symm b)
  have h2 : ‖(EuclideanSpace.equiv (Fin p) ℝ).symm (Z *ᵥ b)‖ ≤
      ‖(EuclideanSpace.equiv (Fin q) ℝ).symm b‖ := by
    calc _ ≤ ‖Z‖ * ‖(EuclideanSpace.equiv (Fin q) ℝ).symm b‖ := by simpa using h
      _ ≤ 1 * _ := by gcongr
      _ = _ := one_mul _
  have h3 := pow_le_pow_left₀ (norm_nonneg _) h2 2
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at h3
  simpa [dotProduct, sq] using h3

theorem trq {a b : ℕ} (x : Fin a → ℝ) (M : Matrix (Fin b) (Fin a) ℝ) (y : Fin b → ℝ) :
    x ⬝ᵥ (Mᵀ *ᵥ y) = (M *ᵥ x) ⬝ᵥ y := by
  rw [dotProduct_mulVec, vecMul_transpose]

theorem symm_part {m p q : ℕ} (L : Matrix (Fin p) (Fin m) ℝ) (R : Matrix (Fin q) (Fin m) ℝ)
    (Z : Matrix (Fin p) (Fin q) ℝ) : (Lᵀ * Z * R + Rᵀ * Zᵀ * L).IsHermitian := by
  unfold IsHermitian
  rw [conjTranspose_eq_transpose_of_trivial]
  simp [transpose_add, transpose_mul, Matrix.mul_assoc, add_comm]

/-- `V` dominates every unit-radius full-block perturbation `LᵀZR + RᵀZᵀL`. -/
def VDom {m p q : ℕ} (L : Matrix (Fin p) (Fin m) ℝ) (R : Matrix (Fin q) (Fin m) ℝ)
    (V : Matrix (Fin m) (Fin m) ℝ) : Prop :=
  ∀ Z : Matrix (Fin p) (Fin q) ℝ, ‖Z‖ ≤ 1 → (V - (Lᵀ * Z * R + Rᵀ * Zᵀ * L)).PosSemidef

lemma VDom_psd {m p q : ℕ} {L : Matrix (Fin p) (Fin m) ℝ} {R : Matrix (Fin q) (Fin m) ℝ}
    {V : Matrix (Fin m) (Fin m) ℝ} (h : VDom L R V) : V.PosSemidef := by
  simpa using h 0 (by simp)

lemma VDom_convex {m p q : ℕ} {L : Matrix (Fin p) (Fin m) ℝ} {R : Matrix (Fin q) (Fin m) ℝ}
    {V V' : Matrix (Fin m) (Fin m) ℝ} (h : VDom L R V) (h' : VDom L R V') {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) : VDom L R (a • V + b • V') := by
  intro Z hZ
  have := ((h Z hZ).smul ha).add ((h' Z hZ).smul hb)
  convert this using 1
  conv_lhs => rw [show (Lᵀ * Z * R + Rᵀ * Zᵀ * L) = (a + b) • (Lᵀ * Z * R + Rᵀ * Zᵀ * L) by
    rw [hab, one_smul]]
  module

lemma VDom_zero_L {m p q : ℕ} (R : Matrix (Fin q) (Fin m) ℝ) :
    VDom (0 : Matrix (Fin p) (Fin m) ℝ) R 0 := by
  intro Z _; simpa using PosSemidef.zero

lemma VDom_zero_R {m p q : ℕ} (L : Matrix (Fin p) (Fin m) ℝ) :
    VDom L (0 : Matrix (Fin q) (Fin m) ℝ) 0 := by
  intro Z _; simpa using PosSemidef.zero

lemma psd_closed {n : ℕ} : IsClosed {X : Matrix (Fin n) (Fin n) ℝ | X.PosSemidef} := by
  have : {X : Matrix (Fin n) (Fin n) ℝ | X.PosSemidef} =
      {X | Xᴴ = X} ∩ ⋂ x : Fin n → ℝ, {X | 0 ≤ star x ⬝ᵥ (X *ᵥ x)} := by
    ext X; simp [posSemidef_iff_dotProduct_mulVec, IsHermitian]
  rw [this]
  refine IsClosed.inter (isClosed_eq (by fun_prop) continuous_id)
    (isClosed_iInter fun x => isClosed_le continuous_const ?_)
  exact continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)

lemma VDom_closed {m p q : ℕ} (L : Matrix (Fin p) (Fin m) ℝ) (R : Matrix (Fin q) (Fin m) ℝ) :
    IsClosed {V : Matrix (Fin m) (Fin m) ℝ | VDom L R V} := by
  have : {V : Matrix (Fin m) (Fin m) ℝ | VDom L R V} =
      ⋂ Z : Matrix (Fin p) (Fin q) ℝ,
        {V | ‖Z‖ ≤ 1 → (V - (Lᵀ * Z * R + Rᵀ * Zᵀ * L)).PosSemidef} := by
    ext V; simp [VDom]
  rw [this]
  refine isClosed_iInter fun Z => ?_
  by_cases hZ : ‖Z‖ ≤ 1
  · simp only [hZ, true_implies]
    exact psd_closed.preimage (by fun_prop)
  · simp only [hZ, false_implies, Set.ofPred_true, isClosed_univ]

/-- Certificate `τLᵀL + τ⁻¹RᵀR` for a full block. -/
lemma VDom_cert {m p q : ℕ} (L : Matrix (Fin p) (Fin m) ℝ) (R : Matrix (Fin q) (Fin m) ℝ)
    (τ : ℝ) (hτ : 0 < τ) : VDom L R (τ • (Lᵀ * L) + τ⁻¹ • (Rᵀ * R)) := by
  intro Z hZ
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · refine IsHermitian.sub ?_ (symm_part L R Z)
    unfold IsHermitian; rw [conjTranspose_eq_transpose_of_trivial]
    simp [transpose_add, transpose_mul, transpose_smul]
  · have hc := opsq Z hZ (R *ᵥ x)
    have hsq : 0 ≤ (τ • (L *ᵥ x) - Z *ᵥ (R *ᵥ x)) ⬝ᵥ (τ • (L *ᵥ x) - Z *ᵥ (R *ᵥ x)) := by
      simpa using dotProduct_star_self_nonneg (τ • (L *ᵥ x) - Z *ᵥ (R *ᵥ x))
    simp only [star_trivial, sub_mulVec, add_mulVec, dotProduct_sub, dotProduct_add, sub_dotProduct,
      smul_mulVec, dotProduct_smul, smul_dotProduct, smul_eq_mul, ← mulVec_mulVec, trq] at hsq ⊢
    have e1 : (L *ᵥ x) ⬝ᵥ (Z *ᵥ (R *ᵥ x)) = (Z *ᵥ (R *ᵥ x)) ⬝ᵥ (L *ᵥ x) := dotProduct_comm _ _
    have e2 : (R *ᵥ x) ⬝ᵥ (Zᵀ *ᵥ (L *ᵥ x)) = (Z *ᵥ (R *ᵥ x)) ⬝ᵥ (L *ᵥ x) := by rw [trq]
    simp only [e1, e2] at hsq ⊢
    clear e1 e2
    generalize (L *ᵥ x) ⬝ᵥ (L *ᵥ x) = AA at *
    generalize (Z *ᵥ (R *ᵥ x)) ⬝ᵥ (L *ᵥ x) = AC at *
    generalize (Z *ᵥ (R *ᵥ x)) ⬝ᵥ (Z *ᵥ (R *ᵥ x)) = CC at *
    generalize (R *ᵥ x) ⬝ᵥ (R *ᵥ x) = BB at *
    have hτ' : 0 < τ⁻¹ := inv_pos.2 hτ
    have key : τ * AA + τ⁻¹ * BB - (AC + AC) = τ⁻¹ * (τ * (τ * AA - AC) - (τ * AC - CC)) +
        τ⁻¹ * (BB - CC) := by
      field_simp; ring
    rw [key]
    exact add_nonneg (mul_nonneg hτ'.le hsq) (mul_nonneg hτ'.le (by linarith))

end MX

end D1

section D2

open Matrix MeasureTheory ProbabilityTheory
open ModernConvex.MatrixCube

namespace MX

lemma gd_eq_prod (n : ℕ) (u : Fin n → ℝ) :
    gaussDensity n u = ∏ i, gaussianPDFReal 0 1 (u i) := by
  simp only [gaussDensity, gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  · rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (by positivity), ← Real.rpow_mul_natCast (by positivity)]
    congr 1; ring
  · rw [← Real.exp_sum]; congr 1
    simp only [neg_div, Finset.sum_div, Finset.sum_neg_distrib]

lemma gd_nonneg (n : ℕ) (u : Fin n → ℝ) : 0 ≤ gaussDensity n u := by
  unfold gaussDensity; positivity

lemma gd_meas (n : ℕ) : Measurable (gaussDensity n) := by
  unfold gaussDensity; fun_prop

lemma gpi (n : ℕ) : Measure.pi (fun _ : Fin n => gaussianReal 0 1) =
    (volume : Measure (Fin n → ℝ)).withDensity
      (fun u => ((Real.toNNReal (gaussDensity n u) : NNReal) : ENNReal)) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  have hφi : Integrable (gaussianPDFReal 0 1) := integrable_gaussianPDFReal 0 1
  have hind : ∀ u : Fin n → ℝ, (Set.univ.pi s).indicator (fun u => gaussDensity n u) u =
      ∏ i, (s i).indicator (gaussianPDFReal 0 1) (u i) := by
    intro u
    by_cases hu : u ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hu, gd_eq_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Set.indicator_of_mem (hu i (Set.mem_univ i))]
    · rw [Set.indicator_of_notMem hu]
      simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hu
      obtain ⟨i, hi⟩ := hu
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm
  have hint : Integrable (fun u : Fin n → ℝ => ∏ i, (s i).indicator (gaussianPDFReal 0 1) ((u : Fin n → ℝ) i)) := by
    rw [volume_pi]
    exact Integrable.fintype_prod (fun i => hφi.indicator (hs i))
  have hm : Measurable (fun u : Fin n → ℝ => Real.toNNReal (gaussDensity n u)) :=
    (gd_meas n).real_toNNReal
  calc ∫⁻ u in Set.univ.pi s, ((Real.toNNReal (gaussDensity n u) : NNReal) : ENNReal)
      = ∫⁻ u, ENNReal.ofReal ((Set.univ.pi s).indicator (fun u => gaussDensity n u) u) := by
        rw [← lintegral_indicator (MeasurableSet.univ_pi hs)]
        refine lintegral_congr fun u => ?_
        by_cases hu : u ∈ Set.univ.pi s
        · simp [Set.indicator_of_mem hu, ENNReal.ofReal]
        · simp [Set.indicator_of_notMem hu]
    _ = ENNReal.ofReal (∫ u : Fin n → ℝ, ∏ i, (s i).indicator (gaussianPDFReal 0 1) (u i)) := by
        simp_rw [hind]
        rw [ofReal_integral_eq_lintegral_ofReal hint]
        exact Filter.Eventually.of_forall fun u => Finset.prod_nonneg fun i _ =>
          Set.indicator_nonneg (fun t _ => gaussianPDFReal_nonneg 0 1 t) _
    _ = ∏ i, ENNReal.ofReal (∫ t, (s i).indicator (gaussianPDFReal 0 1) t) := by
        rw [volume_pi, integral_fintype_prod_eq_prod, ENNReal.ofReal_prod_of_nonneg]
        exact fun i _ => integral_nonneg (Set.indicator_nonneg (fun t _ => gaussianPDFReal_nonneg 0 1 t))
    _ = ∏ i, gaussianReal 0 1 (s i) := by
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [gaussianReal_apply_eq_integral 0 one_ne_zero, integral_indicator (hs i)]

lemma gint (n : ℕ) (g : (Fin n → ℝ) → ℝ) :
    ∫ u, g u ∂(Measure.pi (fun _ : Fin n => gaussianReal 0 1)) = ∫ u, g u * gaussDensity n u := by
  rw [gpi, integral_withDensity_eq_integral_smul (gd_meas n).real_toNNReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp [NNReal.smul_def, Real.coe_toNNReal _ (gd_nonneg n u), mul_comm]

lemma gintegrable (n : ℕ) (g : (Fin n → ℝ) → ℝ)
    (h : Integrable g (Measure.pi (fun _ : Fin n => gaussianReal 0 1))) :
    Integrable (fun u => g u * gaussDensity n u) := by
  rw [gpi, integrable_withDensity_iff_integrable_smul (gd_meas n).real_toNNReal] at h
  refine h.congr (Filter.Eventually.of_forall fun u => ?_)
  simp [NNReal.smul_def, Real.coe_toNNReal _ (gd_nonneg n u), mul_comm]

lemma fb_gauss {p q n : ℕ} (hp : 0 < p) (hq : 0 < q) (hn : 0 < n)
    (L : Matrix (Fin p) (Fin n) ℝ) (R : Matrix (Fin q) (Fin n) ℝ) :
    Integrable (fun u => nrm (L *ᵥ u) * nrm (R *ᵥ u) * gaussDensity n u) ∧
    (2 / Real.pi) * fro L * fro R ≤ ∫ u, nrm (L *ᵥ u) * nrm (R *ᵥ u) * gaussDensity n u := by
  have h := RobustOpt2009.SDPApproximation.proposition_B_4_12.2 p q n hp hq hn L R
  simp only at h
  obtain ⟨hi, hI⟩ := h
  refine ⟨gintegrable n _ hi, ?_⟩
  rw [gint] at hI
  exact hI

end MX

end D2

section D3

open Matrix MeasureTheory
open ModernConvex.MatrixCube

namespace MX

lemma trace_mul_transpose_self {a b : ℕ} (X : Matrix (Fin a) (Fin b) ℝ) :
    (X * Xᵀ).trace = fro X ^ 2 := by
  rw [fro, Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg (X i j))]
  simp [trace, mul_apply, sq]

lemma fro_nonneg {a b : ℕ} (X : Matrix (Fin a) (Fin b) ℝ) : 0 ≤ fro X := Real.sqrt_nonneg _

lemma fro_eq_zero {a b : ℕ} {X : Matrix (Fin a) (Fin b) ℝ} (h : fro X = 0) : X = 0 := by
  rw [fro, Real.sqrt_eq_zero (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    sq_nonneg (X i j))] at h
  ext i j
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg fun j _ =>
    sq_nonneg (X i j))).mp h i (Finset.mem_univ _)
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (X i j))).mp h1 j
    (Finset.mem_univ _)
  simpa using h2

section msepSec

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
attribute [local instance] MC99.sepA_lcs

/-- The set `{ρ(∑Uᵢ + ∑Vⱼ) + P}` of matrices dominated by a certificate. -/
def mS {m s f : ℕ} {p q : Fin f → ℕ} (B : Fin s → Matrix (Fin m) (Fin m) ℝ)
    (L : (j : Fin f) → Matrix (Fin (p j)) (Fin m) ℝ)
    (R : (j : Fin f) → Matrix (Fin (q j)) (Fin m) ℝ) (ρ : ℝ) :
    Set (Matrix (Fin m) (Fin m) ℝ) :=
  {Y | ∃ (U : Fin s → Matrix (Fin m) (Fin m) ℝ) (V : Fin f → Matrix (Fin m) (Fin m) ℝ)
    (P : Matrix (Fin m) (Fin m) ℝ),
    (∀ i, (U i - B i).PosSemidef ∧ (U i + B i).PosSemidef) ∧ (∀ j, VDom (L j) (R j) (V j)) ∧
      P.PosSemidef ∧ Y = ρ • (∑ i, U i + ∑ j, V j) + P}

lemma U_psd {m : ℕ} {U B : Matrix (Fin m) (Fin m) ℝ} (h1 : (U - B).PosSemidef)
    (h2 : (U + B).PosSemidef) : U.PosSemidef := by
  have := (h1.add h2).smul (show (0:ℝ) ≤ 1/2 by norm_num)
  convert this using 1
  ext i j; simp; ring

lemma mS_psd {m s f : ℕ} {p q : Fin f → ℕ} {B : Fin s → Matrix (Fin m) (Fin m) ℝ}
    {L : (j : Fin f) → Matrix (Fin (p j)) (Fin m) ℝ}
    {R : (j : Fin f) → Matrix (Fin (q j)) (Fin m) ℝ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    {Y : Matrix (Fin m) (Fin m) ℝ} (hY : Y ∈ mS B L R ρ) : Y.PosSemidef := by
  obtain ⟨U, V, P, hU, hV, hP, rfl⟩ := hY
  refine (((posSemidef_sum _ fun i _ => U_psd (hU i).1 (hU i).2).add
    (posSemidef_sum _ fun j _ => VDom_psd (hV j))).smul hρ).add hP

lemma mS_add_psd {m s f : ℕ} {p q : Fin f → ℕ} {B : Fin s → Matrix (Fin m) (Fin m) ℝ}
    {L : (j : Fin f) → Matrix (Fin (p j)) (Fin m) ℝ}
    {R : (j : Fin f) → Matrix (Fin (q j)) (Fin m) ℝ} {ρ : ℝ}
    {Y X : Matrix (Fin m) (Fin m) ℝ} (hY : Y ∈ mS B L R ρ) (hX : X.PosSemidef) :
    Y + X ∈ mS B L R ρ := by
  obtain ⟨U, V, P, hU, hV, hP, rfl⟩ := hY
  exact ⟨U, V, P + X, hU, hV, hP.add hX, by rw [add_assoc]⟩

lemma mS_convex {m s f : ℕ} {p q : Fin f → ℕ} (B : Fin s → Matrix (Fin m) (Fin m) ℝ)
    (L : (j : Fin f) → Matrix (Fin (p j)) (Fin m) ℝ)
    (R : (j : Fin f) → Matrix (Fin (q j)) (Fin m) ℝ) (ρ : ℝ) :
    Convex ℝ (mS B L R ρ) := by
  rintro _ ⟨U, V, P, hU, hV, hP, rfl⟩ _ ⟨U', V', P', hU', hV', hP', rfl⟩ a b ha hb hab
  refine ⟨fun i => a • U i + b • U' i, fun j => a • V j + b • V' j, a • P + b • P',
    fun i => ⟨?_, ?_⟩, fun j => VDom_convex (hV j) (hV' j) ha hb hab,
    (hP.smul ha).add (hP'.smul hb), ?_⟩
  · have := ((hU i).1.smul ha).add ((hU' i).1.smul hb)
    convert this using 1
    conv_lhs => rw [show B i = (a + b) • B i by rw [hab, one_smul]]
    module
  · have := ((hU i).2.smul ha).add ((hU' i).2.smul hb)
    convert this using 1
    conv_lhs => rw [show B i = (a + b) • B i by rw [hab, one_smul]]
    module
  · simp only [Finset.sum_add_distrib, ← Finset.smul_sum]
    module

/-- Bounded-trace part, as a set of triples. -/
def mK {m s f : ℕ} {p q : Fin f → ℕ} (B : Fin s → Matrix (Fin m) (Fin m) ℝ)
    (L : (j : Fin f) → Matrix (Fin (p j)) (Fin m) ℝ)
    (R : (j : Fin f) → Matrix (Fin (q j)) (Fin m) ℝ) (ρ T : ℝ) :
    Set ((Fin s → Matrix (Fin m) (Fin m) ℝ) × (Fin f → Matrix (Fin m) (Fin m) ℝ) ×
      Matrix (Fin m) (Fin m) ℝ) :=
  {t | (∀ i, (t.1 i - B i).PosSemidef ∧ (t.1 i + B i).PosSemidef) ∧
    (∀ j, VDom (L j) (R j) (t.2.1 j)) ∧ t.2.2.PosSemidef ∧
    (ρ • (∑ i, t.1 i + ∑ j, t.2.1 j) + t.2.2).trace ≤ T}

lemma mK_closed {m s f : ℕ} {p q : Fin f → ℕ} (B : Fin s → Matrix (Fin m) (Fin m) ℝ)
    (L : (j : Fin f) → Matrix (Fin (p j)) (Fin m) ℝ)
    (R : (j : Fin f) → Matrix (Fin (q j)) (Fin m) ℝ) (ρ T : ℝ) :
    IsClosed (mK B L R ρ T) := by
  have hc : IsClosed {X : Matrix (Fin m) (Fin m) ℝ | X.PosSemidef} := psd_closed
  have h1 : ∀ i, IsClosed {t : (Fin s → Matrix (Fin m) (Fin m) ℝ) ×
      (Fin f → Matrix (Fin m) (Fin m) ℝ) × Matrix (Fin m) (Fin m) ℝ |
      (t.1 i - B i).PosSemidef} := fun i => hc.preimage (by fun_prop)
  have h2 : ∀ i, IsClosed {t : (Fin s → Matrix (Fin m) (Fin m) ℝ) ×
      (Fin f → Matrix (Fin m) (Fin m) ℝ) × Matrix (Fin m) (Fin m) ℝ |
      (t.1 i + B i).PosSemidef} := fun i => hc.preimage (by fun_prop)
  have h3 : ∀ j, IsClosed {t : (Fin s → Matrix (Fin m) (Fin m) ℝ) ×
      (Fin f → Matrix (Fin m) (Fin m) ℝ) × Matrix (Fin m) (Fin m) ℝ |
      VDom (L j) (R j) (t.2.1 j)} := fun j => (VDom_closed (L j) (R j)).preimage (by fun_prop)
  have h4 : IsClosed {t : (Fin s → Matrix (Fin m) (Fin m) ℝ) ×
      (Fin f → Matrix (Fin m) (Fin m) ℝ) × Matrix (Fin m) (Fin m) ℝ |
      t.2.2.PosSemidef} := hc.preimage (by fun_prop)
  have h5 : IsClosed {t : (Fin s → Matrix (Fin m) (Fin m) ℝ) ×
      (Fin f → Matrix (Fin m) (Fin m) ℝ) × Matrix (Fin m) (Fin m) ℝ |
      (ρ • (∑ i, t.1 i + ∑ j, t.2.1 j) + t.2.2).trace ≤ T} :=
    isClosed_le (Continuous.matrix_trace (by fun_prop)) continuous_const
  have : mK B L R ρ T = (⋂ i, ({t : (Fin s → Matrix (Fin m) (Fin m) ℝ) ×
      (Fin f → Matrix (Fin m) (Fin m) ℝ) × Matrix (Fin m) (Fin m) ℝ |
      (t.1 i - B i).PosSemidef} ∩ {t | (t.1 i + B i).PosSemidef})) ∩
      ((⋂ j, {t | VDom (L j) (R j) (t.2.1 j)}) ∩
      ({t | t.2.2.PosSemidef} ∩ {t | (ρ • (∑ i, t.1 i + ∑ j, t.2.1 j) + t.2.2).trace ≤ T})) := by
    ext t; simp [mK, forall_and]
  rw [this]
  exact (isClosed_iInter fun i => (h1 i).inter (h2 i)).inter
    ((isClosed_iInter h3).inter (h4.inter h5))

lemma mK_compact {m s f : ℕ} {p q : Fin f → ℕ} (B : Fin s → Matrix (Fin m) (Fin m) ℝ)
    (L : (j : Fin f) → Matrix (Fin (p j)) (Fin m) ℝ)
    (R : (j : Fin f) → Matrix (Fin (q j)) (Fin m) ℝ) (ρ T : ℝ) (hρ : 0 < ρ) :
    IsCompact (mK B L R ρ T) := by
  refine Metric.isCompact_of_isClosed_isBounded (mK_closed B L R ρ T) ?_
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨T / ρ + T, fun t ht => ?_⟩
  obtain ⟨hU, hV, hP, hT⟩ := ht
  have hUp : ∀ i, (t.1 i).PosSemidef := fun i => U_psd (hU i).1 (hU i).2
  have hVp : ∀ j, (t.2.1 j).PosSemidef := fun j => VDom_psd (hV j)
  have htr : (ρ • (∑ i, t.1 i + ∑ j, t.2.1 j) + t.2.2).trace =
      ρ * (∑ i, (t.1 i).trace + ∑ j, (t.2.1 j).trace) + t.2.2.trace := by
    rw [trace_add, trace_smul, trace_add, trace_sum, trace_sum, smul_eq_mul]
  rw [htr] at hT
  have hsU : 0 ≤ ∑ i, (t.1 i).trace := Finset.sum_nonneg fun i _ => (hUp i).trace_nonneg
  have hsV : 0 ≤ ∑ j, (t.2.1 j).trace := Finset.sum_nonneg fun j _ => (hVp j).trace_nonneg
  have hP0 := hP.trace_nonneg
  have hS : ∑ i, (t.1 i).trace + ∑ j, (t.2.1 j).trace ≤ T / ρ := by
    rw [le_div_iff₀ hρ]; nlinarith
  have hT0 : 0 ≤ T := by nlinarith
  have hTρ : 0 ≤ T / ρ := div_nonneg hT0 hρ.le
  rw [Metric.mem_closedBall, dist_zero_right, norm_prod_le_iff, norm_prod_le_iff]
  refine ⟨?_, ?_, ?_⟩
  · rw [pi_norm_le_iff_of_nonneg (by linarith)]
    intro i
    have : (t.1 i).trace ≤ ∑ i, (t.1 i).trace :=
      Finset.single_le_sum (f := fun i => (t.1 i).trace) (fun i _ => (hUp i).trace_nonneg)
        (Finset.mem_univ i)
    linarith [MC99.sepA_norm_le (hUp i)]
  · rw [pi_norm_le_iff_of_nonneg (by linarith)]
    intro j
    have : (t.2.1 j).trace ≤ ∑ j, (t.2.1 j).trace :=
      Finset.single_le_sum (f := fun j => (t.2.1 j).trace) (fun j _ => (hVp j).trace_nonneg)
        (Finset.mem_univ j)
    linarith [MC99.sepA_norm_le (hVp j)]
  · have : t.2.2.trace ≤ T := by nlinarith
    linarith [MC99.sepA_norm_le hP]

lemma mS_closed {m s f : ℕ} {p q : Fin f → ℕ} (B : Fin s → Matrix (Fin m) (Fin m) ℝ)
    (L : (j : Fin f) → Matrix (Fin (p j)) (Fin m) ℝ)
    (R : (j : Fin f) → Matrix (Fin (q j)) (Fin m) ℝ) (ρ : ℝ) (hρ : 0 < ρ) :
    IsClosed (mS B L R ρ) := by
  refine closure_subset_iff_isClosed.mp fun x hx => ?_
  set T := x.trace + 1
  have hU : IsOpen {Y : Matrix (Fin m) (Fin m) ℝ | Y.trace < T} :=
    isOpen_lt (Continuous.matrix_trace continuous_id) continuous_const
  have hxU : x ∈ {Y : Matrix (Fin m) (Fin m) ℝ | Y.trace < T} := by simp [T]
  have hcomp : IsCompact ((fun t : (Fin s → Matrix (Fin m) (Fin m) ℝ) ×
      (Fin f → Matrix (Fin m) (Fin m) ℝ) × Matrix (Fin m) (Fin m) ℝ =>
        ρ • (∑ i, t.1 i + ∑ j, t.2.1 j) + t.2.2) '' mK B L R ρ T) :=
    (mK_compact B L R ρ T hρ).image (by fun_prop)
  have h1 : x ∈ closure ({Y : Matrix (Fin m) (Fin m) ℝ | Y.trace < T} ∩ mS B L R ρ) :=
    hU.inter_closure ⟨hxU, hx⟩
  have h2 : {Y : Matrix (Fin m) (Fin m) ℝ | Y.trace < T} ∩ mS B L R ρ ⊆
      (fun t : (Fin s → Matrix (Fin m) (Fin m) ℝ) ×
      (Fin f → Matrix (Fin m) (Fin m) ℝ) × Matrix (Fin m) (Fin m) ℝ =>
        ρ • (∑ i, t.1 i + ∑ j, t.2.1 j) + t.2.2) '' mK B L R ρ T := by
    rintro _ ⟨hlt, U, V, P, hUB, hV, hP, rfl⟩
    exact ⟨(U, V, P), ⟨hUB, hV, hP, le_of_lt hlt⟩, rfl⟩
  obtain ⟨t, ht, rfl⟩ := hcomp.isClosed.closure_subset (closure_mono h2 h1)
  exact ⟨t.1, t.2.1, t.2.2, ht.1, ht.2.1, ht.2.2.1, rfl⟩

/-- Full-block certificate adapted to a congruence `M`: trace bound `2‖LM‖_F‖RM‖_F`. -/
lemma fb_choice {m p q : ℕ} (L : Matrix (Fin p) (Fin m) ℝ) (R : Matrix (Fin q) (Fin m) ℝ)
    (M N : Matrix (Fin m) (Fin m) ℝ) (hMN : M * N = 1) :
    ∃ V : Matrix (Fin m) (Fin m) ℝ, VDom L R V ∧
      (M * Mᵀ * V).trace ≤ 2 * fro (L * M) * fro (R * M) := by
  by_cases h0 : fro (L * M) = 0 ∨ fro (R * M) = 0
  · refine ⟨0, ?_, by simpa using mul_nonneg (mul_nonneg zero_le_two (fro_nonneg (L * M))) (fro_nonneg (R * M))⟩
    rcases h0 with h | h
    · have hL : L = 0 := by
        have := congrArg (· * N) (fro_eq_zero h)
        simpa [Matrix.mul_assoc, hMN] using this
      subst hL; exact VDom_zero_L R
    · have hR : R = 0 := by
        have := congrArg (· * N) (fro_eq_zero h)
        simpa [Matrix.mul_assoc, hMN] using this
      subst hR; exact VDom_zero_R L
  · push Not at h0
    obtain ⟨ha, hb⟩ := h0
    have ha' : 0 < fro (L * M) := lt_of_le_of_ne (fro_nonneg _) (Ne.symm ha)
    have hb' : 0 < fro (R * M) := lt_of_le_of_ne (fro_nonneg _) (Ne.symm hb)
    set τ := fro (R * M) / fro (L * M)
    have hτ : 0 < τ := div_pos hb' ha'
    refine ⟨_, VDom_cert L R τ hτ, le_of_eq ?_⟩
    have e1 : (M * Mᵀ * (Lᵀ * L)).trace = fro (L * M) ^ 2 := by
      rw [← Matrix.mul_assoc, trace_mul_comm, ← trace_mul_transpose_self, transpose_mul]
      simp only [Matrix.mul_assoc]
    have e2 : (M * Mᵀ * (Rᵀ * R)).trace = fro (R * M) ^ 2 := by
      rw [← Matrix.mul_assoc, trace_mul_comm, ← trace_mul_transpose_self, transpose_mul]
      simp only [Matrix.mul_assoc]
    rw [Matrix.mul_add, trace_add, Matrix.mul_smul, Matrix.mul_smul, trace_smul, trace_smul, e1, e2,
      smul_eq_mul, smul_eq_mul]
    simp only [τ]
    field_simp
    ring

/-- Mixed-block separation: if the certificate system fails, some congruence `M` makes
the trace of `B₀` smaller than `ρ` times the certificate bound. -/
theorem msep {m s f : ℕ} {p q : Fin f → ℕ} (B₀ : Matrix (Fin m) (Fin m) ℝ)
    (B : Fin s → Matrix (Fin m) (Fin m) ℝ)
    (L : (j : Fin f) → Matrix (Fin (p j)) (Fin m) ℝ)
    (R : (j : Fin f) → Matrix (Fin (q j)) (Fin m) ℝ)
    (hB₀ : B₀.PosSemidef) (hB : ∀ i, (B i).IsHermitian) (ρ : ℝ) (hρ : 0 < ρ)
    (hS : B₀ ∉ mS B L R ρ) :
    ∃ M : Matrix (Fin m) (Fin m) ℝ,
      (Mᵀ * B₀ * M).trace < ρ * (∑ i, eigL1 (Mᵀ * B i * M) +
        ∑ j, 2 * fro (L j * M) * fro (R j * M)) := by
  classical
  obtain ⟨g, u, hgA, hgS⟩ :=
    geometric_hahn_banach_point_closed (mS_convex B L R ρ) (mS_closed B L R ρ hρ) hS
  obtain ⟨W, hWh, hW⟩ := MC99.sepA_lin (g : Matrix (Fin m) (Fin m) ℝ →ₗ[ℝ] ℝ)
  have hSh : ∀ c ∈ mS B L R ρ, c.IsHermitian := fun c hc => (mS_psd hρ.le hc).isHermitian
  have hWS : ∀ c ∈ mS B L R ρ, u < (W * c).trace := fun c hc => by
    rw [← hW c (hSh c hc)]; exact hgS c hc
  have hWA : (W * B₀).trace < u := by rw [← hW B₀ hB₀.isHermitian]; exact hgA
  have hS0 : ∀ c ∈ mS B L R ρ, 0 ≤ c.trace := fun c hc => (mS_psd hρ.le hc).trace_nonneg
  -- a member of S
  choose Q hQ1 hQ2 _ using fun i => MC99.sepA_abs (B i) (hB i)
  have hc0 : ρ • (∑ i, Q i + ∑ j, ((1 : ℝ) • ((L j)ᵀ * L j) + (1 : ℝ)⁻¹ • ((R j)ᵀ * R j))) +
      0 ∈ mS B L R ρ :=
    ⟨Q, fun j => (1 : ℝ) • ((L j)ᵀ * L j) + (1 : ℝ)⁻¹ • ((R j)ᵀ * R j), 0,
      fun i => ⟨hQ1 i, hQ2 i⟩, fun j => VDom_cert (L j) (R j) 1 one_pos, PosSemidef.zero, rfl⟩
  set c0 := ρ • (∑ i, Q i + ∑ j, ((1 : ℝ) • ((L j)ᵀ * L j) + (1 : ℝ)⁻¹ • ((R j)ᵀ * R j))) + 0
  have hWpsd : W.PosSemidef := by
    refine PosSemidef.of_dotProduct_mulVec_nonneg hWh fun v => ?_
    by_contra hneg
    push Not at hneg
    set qv := star v ⬝ᵥ (W *ᵥ v) with hq
    have hV : (vecMulVec v v).PosSemidef := by
      simpa using posSemidef_vecMulVec_self_star v
    set t : ℝ := ((W * c0).trace - u) / (-qv) + 1 with ht_def
    have ht : 0 ≤ t := by
      have : 0 ≤ ((W * c0).trace - u) / (-qv) :=
        div_nonneg (by linarith [hWS c0 hc0]) (by linarith)
      linarith
    have hmem := mS_add_psd hc0 (hV.smul ht)
    have h := hWS _ hmem
    rw [Matrix.mul_add, trace_add, Matrix.mul_smul, trace_smul, MC99.sepA_trace_vv,
      smul_eq_mul] at h
    have e : t * qv = u - (W * c0).trace + qv := by
      have hq0 : qv ≠ 0 := hneg.ne
      rw [ht_def]; field_simp; ring
    rw [← hq] at h
    linarith
  set δ := u - (W * B₀).trace
  have hδ : 0 < δ := by simp only [δ]; linarith
  have htA := hB₀.trace_nonneg
  set ε := δ / (B₀.trace + 1)
  have hε : 0 < ε := div_pos hδ (by linarith)
  have hεA : ε * B₀.trace < δ := by
    have : ε * (B₀.trace + 1) = δ := div_mul_cancel₀ _ (by linarith)
    nlinarith
  -- spectral decomposition of W
  obtain ⟨U, h1, h2, hWU⟩ := MC99.sepA_spec W hWh
  have hl : ∀ k, 0 ≤ hWh.eigenvalues k := hWpsd.eigenvalues_nonneg
  generalize hWh.eigenvalues = l at hWU hl
  set d : Fin m → ℝ := fun k => l k + ε with hd_def
  have hd : ∀ k, 0 < d k := fun k => by simp only [d]; linarith [hl k]
  set M := U * diagonal (fun k => Real.sqrt (d k)) with hM_def
  set N := diagonal (fun k => 1 / Real.sqrt (d k)) * Uᵀ with hN_def
  have hsq : ∀ k, Real.sqrt (d k) * Real.sqrt (d k) = d k :=
    fun k => Real.mul_self_sqrt (hd k).le
  have hsq0 : ∀ k, Real.sqrt (d k) ≠ 0 := fun k => (Real.sqrt_pos.2 (hd k)).ne'
  have hNM : N * M = 1 := by
    rw [hN_def, hM_def, Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ, h1, Matrix.one_mul,
      diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext k; field_simp [hsq0 k]
  have hMN : M * N = 1 := by
    rw [hN_def, hM_def, Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal _) (diagonal _),
      diagonal_mul_diagonal]
    have : (diagonal fun k => Real.sqrt (d k) * (1 / Real.sqrt (d k))) = 1 := by
      rw [← diagonal_one]; congr 1; funext k; field_simp [hsq0 k]
    rw [this, Matrix.one_mul, h2]
  have hMM : M * Mᵀ = U * diagonal d * Uᵀ := by
    rw [hM_def, transpose_mul, diagonal_transpose, Matrix.mul_assoc,
      ← Matrix.mul_assoc (diagonal _) (diagonal _), diagonal_mul_diagonal, ← Matrix.mul_assoc]
    congr 3; funext k; exact hsq k
  have hdiag : diagonal d = diagonal l + ε • (1 : Matrix (Fin m) (Fin m) ℝ) := by
    ext i j; by_cases hij : i = j
    · subst hij; simp [d]
    · simp [hij, one_apply]
  have hWε : W + ε • (1 : Matrix (Fin m) (Fin m) ℝ) = M * Mᵀ := by
    rw [hMM, hdiag, Matrix.mul_add, Matrix.add_mul, ← hWU, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, h2]
  have hBt : ∀ i, (Mᵀ * B i * M).IsHermitian := fun i => by
    simpa [conjTranspose_eq_transpose_of_trivial] using isHermitian_conjTranspose_mul_mul M (hB i)
  choose Rr hR1 hR2 hR3 using fun i => MC99.sepA_abs _ (hBt i)
  have hNB : ∀ i, Nᵀ * (Mᵀ * B i * M) * N = B i := by
    intro i
    calc Nᵀ * (Mᵀ * B i * M) * N = (M * N)ᵀ * B i * (M * N) := by
          simp only [transpose_mul, Matrix.mul_assoc]
      _ = B i := by rw [hMN]; simp
  choose Vs hVs1 hVs2 using fun j => fb_choice (L j) (R j) M N hMN
  set c := ρ • (∑ i, Nᵀ * Rr i * N + ∑ j, Vs j) + 0 with hc_def
  have hc : c ∈ mS B L R ρ := by
    refine ⟨fun i => Nᵀ * Rr i * N, Vs, 0, fun i => ⟨?_, ?_⟩, hVs1, PosSemidef.zero, rfl⟩
    · have := (hR1 i).conjTranspose_mul_mul_same N
      rw [conjTranspose_eq_transpose_of_trivial, Matrix.mul_sub, Matrix.sub_mul, hNB] at this
      exact this
    · have := (hR2 i).conjTranspose_mul_mul_same N
      rw [conjTranspose_eq_transpose_of_trivial, Matrix.mul_add, Matrix.add_mul, hNB] at this
      exact this
  have hRtr : ∀ i, (M * Mᵀ * (Nᵀ * Rr i * N)).trace = eigL1 (Mᵀ * B i * M) := by
    intro i
    rw [← hR3 i]
    calc (M * Mᵀ * (Nᵀ * Rr i * N)).trace = (M * (N * M)ᵀ * Rr i * N).trace := by
          simp only [transpose_mul, Matrix.mul_assoc]
      _ = (Rr i).trace := by
          rw [hNM, transpose_one, Matrix.mul_one, trace_mul_comm, ← Matrix.mul_assoc, hNM,
            Matrix.one_mul]
  have htc : ((W + ε • (1 : Matrix (Fin m) (Fin m) ℝ)) * c).trace ≤
      ρ * (∑ i, eigL1 (Mᵀ * B i * M) + ∑ j, 2 * fro (L j * M) * fro (R j * M)) := by
    rw [hWε, hc_def, add_zero, Matrix.mul_smul, trace_smul, smul_eq_mul, Matrix.mul_add,
      trace_add, Matrix.mul_sum, Matrix.mul_sum, trace_sum, trace_sum]
    refine mul_le_mul_of_nonneg_left (add_le_add (le_of_eq (Finset.sum_congr rfl
      fun i _ => hRtr i)) (Finset.sum_le_sum fun j _ => hVs2 j)) hρ.le
  have htA' : ((W + ε • (1 : Matrix (Fin m) (Fin m) ℝ)) * B₀).trace = (Mᵀ * B₀ * M).trace := by
    rw [hWε, Matrix.mul_assoc, trace_mul_comm]
  refine ⟨M, ?_⟩
  rw [← htA']
  refine lt_of_lt_of_le ?_ htc
  have e : ∀ Y : Matrix (Fin m) (Fin m) ℝ,
      ((W + ε • (1 : Matrix (Fin m) (Fin m) ℝ)) * Y).trace = (W * Y).trace + ε * Y.trace := by
    intro Y
    rw [Matrix.add_mul, trace_add, Matrix.smul_mul, Matrix.one_mul, trace_smul, smul_eq_mul]
  rw [e, e]
  have h1 := hWS c hc
  have h2 : 0 ≤ ε * c.trace := mul_nonneg hε.le (hS0 c hc)
  simp only [δ] at hεA
  linarith

end msepSec

end MX

end D3

section D4

open Matrix MeasureTheory
open ModernConvex.MatrixCube
open scoped Matrix.Norms.L2Operator

namespace MX

lemma theta_zero : theta 0 = 0 := by
  unfold theta
  have : {α : Fin 0 → ℝ | ∑ i, |α i| = 1} = ∅ := by
    ext α; simp
  rw [this, Set.image_empty, Real.sInf_empty, div_zero]

lemma theta_monotone : Monotone theta := by
  intro a b hab
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · rw [theta_zero]; exact MC99.theta_nonneg b
  · exact MC99.theta_mono ha hab

lemma theta_le (μ : ℕ) (hμ : 2 ≤ μ) : theta μ ≤ Real.pi * Real.sqrt ((μ : ℝ) / 2) := by
  have h1 := theta_bounds.1 μ (by omega)
  refine h1.trans ?_
  rw [Real.sqrt_div (Nat.cast_nonneg μ)]
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have hs2' : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hμ0 : 0 ≤ Real.sqrt (μ : ℝ) := Real.sqrt_nonneg _
  rw [mul_div_assoc]
  apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
  exact div_le_div_of_nonneg_left hμ0 hs2 hs2'

lemma dot_vecMulVec {p q : ℕ} (a : Fin p → ℝ) (b : Fin q → ℝ) (c : ℝ) :
    a ⬝ᵥ ((c • vecMulVec a b) *ᵥ b) = c * (nrm a ^ 2 * nrm b ^ 2) := by
  rw [nrm_sq, nrm_sq, smul_mulVec, vecMulVec_mulVec]
  simp only [dotProduct_smul, op_smul_eq_smul, smul_eq_mul]
  ring

end MX

open MX

/-- ρ = 0 certificate for a scalar block. -/
lemma MX.scal_cert0 {m : ℕ} (B : Matrix (Fin m) (Fin m) ℝ) (hB : B.IsHermitian) :
    ((1 / 2 : ℝ) • (B * B + 1) - B).PosSemidef ∧ ((1 / 2 : ℝ) • (B * B + 1) + B).PosSemidef := by
  have hA := (posSemidef_conjTranspose_mul_self (B - 1)).smul (by norm_num : (0:ℝ) ≤ 1 / 2)
  have hC := (posSemidef_conjTranspose_mul_self (B + 1)).smul (by norm_num : (0:ℝ) ≤ 1 / 2)
  rw [conjTranspose_sub, hB.eq, conjTranspose_one] at hA
  rw [conjTranspose_add, hB.eq, conjTranspose_one] at hC
  refine ⟨?_, ?_⟩
  · convert hA using 1
    simp only [sub_mul, mul_sub, Matrix.one_mul, Matrix.mul_one]
    module
  · convert hC using 1
    simp only [add_mul, mul_add, Matrix.one_mul, Matrix.mul_one]
    module

theorem solution :
    ∃ θ : ℕ → ℝ, Monotone θ ∧ θ 2 = Real.pi / 2 ∧ θ 4 = 2 ∧
      (∀ μ : ℕ, 2 ≤ μ → θ μ ≤ Real.pi * Real.sqrt ((μ : ℝ) / 2)) ∧
      ∀ (m s f : ℕ), 0 < m → ∀ (p q : Fin f → ℕ),
      (∀ j, 0 < p j) → (∀ j, 0 < q j) →
      ∀ (B₀ : Matrix (Fin m) (Fin m) ℝ) (B : Fin s → Matrix (Fin m) (Fin m) ℝ)
        (L : (j : Fin f) → Matrix (Fin (p j)) (Fin m) ℝ)
        (R : (j : Fin f) → Matrix (Fin (q j)) (Fin m) ℝ),
      B₀.IsHermitian → (∀ i, (B i).IsHermitian) → ∀ ρ : ℝ, 0 ≤ ρ →
      let a : ℝ → Prop := fun r =>
        ∀ (z : Fin s → ℝ) (Z : (j : Fin f) → Matrix (Fin (p j)) (Fin (q j)) ℝ),
          (∀ i, |z i| ≤ r) → (∀ j, ‖Z j‖ ≤ r) →
          (B₀ + (∑ i, z i • B i) +
            ∑ j, ((L j)ᵀ * Z j * R j + (R j)ᵀ * (Z j)ᵀ * L j)).PosSemidef
      let b : Prop :=
        ∃ (U : Fin s → Matrix (Fin m) (Fin m) ℝ)
          (V : Fin f → Matrix (Fin m) (Fin m) ℝ),
          (∀ i, (U i).IsHermitian) ∧ (∀ j, (V j).IsHermitian) ∧
          (∀ i, (U i - B i).PosSemidef ∧ (U i + B i).PosSemidef) ∧
          (∀ j, ∀ Z : Matrix (Fin (p j)) (Fin (q j)) ℝ, ‖Z‖ ≤ 1 →
            (V j - ((L j)ᵀ * Z * R j + (R j)ᵀ * Zᵀ * L j)).PosSemidef) ∧
          (B₀ - ρ • (∑ i, U i) - ρ • (∑ j, V j)).PosSemidef
      ∀ μ : ℕ, 2 ≤ μ → (∀ i, (B i).rank ≤ μ) → ¬ b → ¬ a (θ μ * ρ) := by
  refine ⟨theta, theta_monotone, theta_bounds.2, RobustOpt2009.SDPApproximation.theta_four,
    theta_le, ?_⟩
  intro m s f hm p q hp hq B₀ B L R hB₀ hB ρ hρ a b μ hμ hrank hnb ha
  set θ := theta μ with hθdef
  have hθ0 : 0 ≤ θ := MC99.theta_nonneg μ
  have hθpi : Real.pi / 2 ≤ θ := by
    rw [← theta_bounds.2]; exact MC99.theta_mono (by norm_num) hμ
  have hθρ : 0 ≤ θ * ρ := mul_nonneg hθ0 hρ
  have hB₀psd : B₀.PosSemidef := by
    simpa using ha 0 0 (fun i => by simpa using hθρ) (fun j => by simpa using hθρ)
  have hUherm : ∀ {U B' : Matrix (Fin m) (Fin m) ℝ}, (U - B').PosSemidef → (U + B').PosSemidef →
      U.IsHermitian := fun h1 h2 => (MX.U_psd h1 h2).isHermitian
  rcases hρ.lt_or_eq with hρ' | hρ'
  swap
  · -- ρ = 0: the certificate system is always solvable when B₀ ⪰ 0
    subst hρ'
    apply hnb
    refine ⟨fun i => (1 / 2 : ℝ) • (B i * B i + 1), fun j => (L j)ᵀ * L j + (R j)ᵀ * R j,
      fun i => hUherm (MX.scal_cert0 (B i) (hB i)).1 (MX.scal_cert0 (B i) (hB i)).2,
      fun j => ?_, fun i => MX.scal_cert0 (B i) (hB i), fun j Z hZ => ?_, by simpa using hB₀psd⟩
    · have := VDom_psd (VDom_cert (L j) (R j) 1 one_pos)
      simpa using this.isHermitian
    · have := VDom_cert (L j) (R j) 1 one_pos Z hZ
      simpa using this
  -- ρ > 0
  have hS : B₀ ∉ mS B L R ρ := by
    rintro ⟨U, V, P, hU, hV, hP, hY⟩
    apply hnb
    refine ⟨U, V, fun i => hUherm (hU i).1 (hU i).2, fun j => (VDom_psd (hV j)).isHermitian,
      hU, hV, ?_⟩
    rw [hY, smul_add]; convert hP using 1; abel
  obtain ⟨M, hM⟩ := msep B₀ B L R hB₀psd hB ρ hρ' hS
  -- Gaussian randomization
  set Bt : Fin s → Matrix (Fin m) (Fin m) ℝ := fun i => Mᵀ * B i * M with hBt
  set Bt₀ := Mᵀ * B₀ * M with hBt₀
  have hBth : ∀ i, (Bt i).IsHermitian := fun i => by
    simpa [Bt, conjTranspose_eq_transpose_of_trivial] using
      isHermitian_conjTranspose_mul_mul M (hB i)
  have hBt₀h : Bt₀.IsHermitian := by
    simpa [Bt₀, conjTranspose_eq_transpose_of_trivial] using
      isHermitian_conjTranspose_mul_mul M hB₀
  have hrk : ∀ i, (Bt i).rank ≤ μ := fun i =>
    ((rank_mul_le_left _ _).trans (rank_mul_le_right _ _)).trans (hrank i)
  set g := gaussDensity m with hg
  set qf : Fin s → (Fin m → ℝ) → ℝ := fun i u => u ⬝ᵥ (Bt i *ᵥ u) with hqf
  set hf : Fin f → (Fin m → ℝ) → ℝ := fun j u => nrm ((L j * M) *ᵥ u) * nrm ((R j * M) *ᵥ u)
    with hhf
  have hfi : ∀ j, Integrable (fun u => hf j u * g u) := fun j =>
    (fb_gauss (hp j) (hq j) hm (L j * M) (R j * M)).1
  set F : (Fin m → ℝ) → ℝ := fun u =>
    (u ⬝ᵥ (Bt₀ *ᵥ u)) * g u - θ * ρ * (∑ i, |qf i u| * g u + ∑ j, 2 * (hf j u * g u)) with hF
  have hint : ∫ u, F u = Bt₀.trace - θ * ρ * ((∑ i, (∫ u, |qf i u| * g u)) +
      ∑ j, 2 * (∫ u, hf j u * g u)) := by
    simp only [hF]
    rw [integral_sub (MC99.integrable_quad Bt₀), integral_const_mul, integral_add,
      integral_finsetSum, integral_finsetSum]
    · rw [(gaussian_quadratic_form Bt₀ hBt₀h).1]
      simp only [integral_const_mul]
    · intro j _; exact (hfi j).const_mul 2
    · intro i _; exact MC99.mn_int_abs (Bt i)
    · exact integrable_finsetSum _ fun i _ => MC99.mn_int_abs (Bt i)
    · exact integrable_finsetSum _ fun j _ => (hfi j).const_mul 2
    · exact (integrable_finsetSum _ fun i _ => MC99.mn_int_abs (Bt i)).add
        (integrable_finsetSum _ fun j _ => (hfi j).const_mul 2) |>.const_mul _
  have hneg : ∫ u, F u < 0 := by
    rw [hint]
    have h1 : ∀ i, eigL1 (Bt i) ≤ θ * (∫ u, |qf i u| * g u) := fun i =>
      MC99.gauss_le (Bt i) (hBth i) μ (hrk i)
    have h2 : ∀ j, 2 * fro (L j * M) * fro (R j * M) ≤ θ * (2 * (∫ u, hf j u * g u)) := by
      intro j
      have hb := (fb_gauss (hp j) (hq j) hm (L j * M) (R j * M)).2
      have hI0 : 0 ≤ ∫ u, hf j u * g u := integral_nonneg fun u =>
        mul_nonneg (mul_nonneg (nrm_nonneg _) (nrm_nonneg _)) (MC99.mn_gd_nonneg m u)
      have hpi := Real.pi_pos
      have : fro (L j * M) * fro (R j * M) ≤ (Real.pi / 2) * (∫ u, hf j u * g u) := by
        have e : fro (L j * M) * fro (R j * M) =
            (Real.pi / 2) * ((2 / Real.pi) * fro (L j * M) * fro (R j * M)) := by
          field_simp
        rw [e]
        exact mul_le_mul_of_nonneg_left hb (by positivity)
      nlinarith [mul_le_mul_of_nonneg_right hθpi hI0]
    have hsum : ρ * (∑ i, eigL1 (Bt i) + ∑ j, 2 * fro (L j * M) * fro (R j * M)) ≤
        θ * ρ * ((∑ i, (∫ u, |qf i u| * g u)) + ∑ j, 2 * (∫ u, hf j u * g u)) := by
      have := add_le_add (Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => h1 i)
        (Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => h2 j)
      rw [← Finset.mul_sum, ← Finset.mul_sum, ← mul_add] at this
      nlinarith [mul_le_mul_of_nonneg_left this hρ]
    have := hM
    simp only [Bt₀, Bt] at hsum ⊢
    linarith
  obtain ⟨u, hu⟩ : ∃ u, F u < 0 := by
    by_contra hcon
    push Not at hcon
    exact absurd (integral_nonneg hcon) (not_le.mpr hneg)
  have hFu : u ⬝ᵥ (Bt₀ *ᵥ u) - θ * ρ * (∑ i, |qf i u| + ∑ j, 2 * hf j u) < 0 := by
    have hp0 := MC99.mn_gd_nonneg m u
    have : F u = (u ⬝ᵥ (Bt₀ *ᵥ u) - θ * ρ * (∑ i, |qf i u| + ∑ j, 2 * hf j u)) * g u := by
      simp only [hF, Finset.sum_mul, sub_mul, add_mul, mul_add, Finset.mul_sum, mul_assoc]
    rw [this] at hu
    by_contra hc; push Not at hc
    exact absurd (mul_nonneg hc hp0) (not_le.mpr hu)
  -- the bad perturbation
  set x := M *ᵥ u with hx
  set z : Fin s → ℝ := fun i => if 0 ≤ qf i u then -(θ * ρ) else θ * ρ with hz
  have hzq : ∀ i, z i * qf i u = -(θ * ρ * |qf i u|) := fun i => by
    simp only [hz]; split_ifs with h
    · rw [abs_of_nonneg h]; ring
    · rw [abs_of_neg (not_le.mp h)]; ring
  have hzabs : ∀ i, |z i| ≤ θ * ρ := fun i => by
    simp only [hz]; split_ifs <;> simp [abs_of_nonneg hθρ]
  set Z : (j : Fin f) → Matrix (Fin (p j)) (Fin (q j)) ℝ := fun j =>
    if nrm (L j *ᵥ x) * nrm (R j *ᵥ x) = 0 then 0 else
      (-(θ * ρ) / (nrm (L j *ᵥ x) * nrm (R j *ᵥ x))) • vecMulVec (L j *ᵥ x) (R j *ᵥ x) with hZ
  have hZn : ∀ j, ‖Z j‖ ≤ θ * ρ := by
    intro j
    simp only [hZ]
    split_ifs with h0
    · simpa using hθρ
    · have hpos : 0 < nrm (L j *ᵥ x) * nrm (R j *ᵥ x) :=
        lt_of_le_of_ne (mul_nonneg (nrm_nonneg _) (nrm_nonneg _)) (Ne.symm h0)
      rw [norm_smul, Real.norm_eq_abs, abs_div, abs_neg, abs_of_nonneg hθρ, abs_of_pos hpos]
      calc θ * ρ / (nrm (L j *ᵥ x) * nrm (R j *ᵥ x)) * ‖vecMulVec (L j *ᵥ x) (R j *ᵥ x)‖
          ≤ θ * ρ / (nrm (L j *ᵥ x) * nrm (R j *ᵥ x)) * (nrm (L j *ᵥ x) * nrm (R j *ᵥ x)) :=
            mul_le_mul_of_nonneg_left (opnorm_vecMulVec _ _) (div_nonneg hθρ hpos.le)
        _ = θ * ρ := div_mul_cancel₀ _ hpos.ne'
  have hZq : ∀ j, (L j *ᵥ x) ⬝ᵥ (Z j *ᵥ (R j *ᵥ x)) = -(θ * ρ) * hf j u := by
    intro j
    have e1 : (L j * M) *ᵥ u = L j *ᵥ x := by rw [hx, mulVec_mulVec]
    have e2 : (R j * M) *ᵥ u = R j *ᵥ x := by rw [hx, mulVec_mulVec]
    simp only [hhf, e1, e2, hZ]
    split_ifs with h0
    · rw [h0]; simp
    · rw [dot_vecMulVec]
      field_simp
  have hpsd := ha z Z hzabs hZn
  have h0 := hpsd.dotProduct_mulVec_nonneg x
  simp only [star_trivial] at h0
  have hexp : x ⬝ᵥ ((B₀ + ∑ i, z i • B i +
      ∑ j, ((L j)ᵀ * Z j * R j + (R j)ᵀ * (Z j)ᵀ * L j)) *ᵥ x) =
      u ⬝ᵥ (Bt₀ *ᵥ u) + ∑ i, z i * qf i u + ∑ j, 2 * ((L j *ᵥ x) ⬝ᵥ (Z j *ᵥ (R j *ᵥ x))) := by
    simp only [add_mulVec, dotProduct_add, sum_mulVec, dotProduct_sum, smul_mulVec,
      dotProduct_smul, smul_eq_mul]
    congr 1
    congr 1
    · rw [hx, MC99.mn_quad]
    · refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hqf, Bt]
      rw [hx, MC99.mn_quad]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [← mulVec_mulVec, ← mulVec_mulVec, trq, ← mulVec_mulVec, ← mulVec_mulVec, trq, trq,
        dotProduct_comm (Z j *ᵥ (R j *ᵥ x))]
      ring
  rw [hexp] at h0
  have hs1 : ∑ i, z i * qf i u = -(θ * ρ * ∑ i, |qf i u|) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun i _ => hzq i
  have hs2 : ∑ j, 2 * ((L j *ᵥ x) ⬝ᵥ (Z j *ᵥ (R j *ᵥ x))) = -(θ * ρ * ∑ j, 2 * hf j u) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [hZq]; ring
  rw [hs1, hs2] at h0
  linarith

end D4
