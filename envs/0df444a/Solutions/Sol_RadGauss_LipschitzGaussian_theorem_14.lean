-- Prove2me | solution 1 for RadGauss.LipschitzGaussian.theorem_14
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:45:07.835572+00:00
-- url     : https://prove2.me/submissions/198c1e2d-f9bd-4306-a321-208bd7949376

import Mathlib
import Definitions.Def_RadGauss_LipschitzGaussian_GaussianComplexity
import Definitions.Def_RadGauss_LipschitzGaussian_Classes
import Theorems.Thm_HighDimProb_RandomProcesses_sudakov_fernique_finite_dim

open MeasureTheory ProbabilityTheory Complex
open scoped ENNReal NNReal Matrix

namespace TG14

/-- characteristic integral of a linear form of iid standard Gaussians. -/
lemma integral_cexp_linear {κ : Type*} [Fintype κ] (c : κ → ℝ) :
    ∫ u : κ → ℝ, cexp ((∑ k, c k * u k : ℝ) * I) ∂(Measure.pi fun _ : κ => gaussianReal 0 1)
      = cexp (-(∑ k, c k ^ 2 : ℝ) / 2) := by
  have h := integral_fintype_prod_eq_prod (𝕜 := ℂ)
    (fun k (x : ℝ) => cexp ((c k * x : ℝ) * I)) (μ := fun _ : κ => gaussianReal 0 1)
  have h2 : ∀ k, ∫ x, cexp ((c k * x : ℝ) * I) ∂gaussianReal 0 1 = cexp (-(c k ^ 2 : ℝ) / 2) := by
    intro k
    have := charFun_gaussianReal (μ := 0) (v := 1) (c k)
    rw [charFun_apply_real] at this
    push_cast at this ⊢
    rw [this]; congr 1; ring
  calc ∫ u : κ → ℝ, cexp ((∑ k, c k * u k : ℝ) * I) ∂(Measure.pi fun _ : κ => gaussianReal 0 1)
      = ∫ u : κ → ℝ, ∏ k, cexp ((c k * u k : ℝ) * I)
          ∂(Measure.pi fun _ : κ => gaussianReal 0 1) := by
        congr 1 with u
        rw [← Complex.exp_sum]
        congr 1
        push_cast
        rw [Finset.sum_mul]
    _ = ∏ k, cexp (-(c k ^ 2 : ℝ) / 2) := by rw [h]; simp only [h2]
    _ = cexp (-(∑ k, c k ^ 2 : ℝ) / 2) := by
        rw [← Complex.exp_sum]
        congr 1
        push_cast
        simp only [neg_div, Finset.sum_neg_distrib, Finset.sum_div]

open scoped RealInnerProductSpace in
lemma map_pi_gaussian_linear {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (A : Matrix ι κ ℝ) :
    (Measure.pi fun _ : κ => gaussianReal 0 1).map (fun u => WithLp.toLp 2 (A *ᵥ u)) =
      multivariateGaussian 0 (A * A.transpose) := by
  have hPSD : (A * A.transpose).PosSemidef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose A
  have hmeas : Measurable (fun u : κ → ℝ => WithLp.toLp 2 (A *ᵥ u)) :=
    ((PiLp.continuous_toLp 2 _).comp (Continuous.matrix_mulVec continuous_const continuous_id)).measurable
  apply Measure.ext_of_charFun
  funext s
  rw [charFun_multivariateGaussian hPSD, charFun_apply,
    integral_map hmeas.aemeasurable (by fun_prop)]
  have hinner : ∀ u : κ → ℝ,
      ⟪WithLp.toLp 2 (A *ᵥ u), s⟫ = ∑ k, (A.transpose *ᵥ s.ofLp) k * u k := by
    intro u
    simp only [PiLp.inner_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
      RCLike.inner_apply, conj_trivial, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  simp_rw [hinner]
  rw [integral_cexp_linear]
  have hq : ∑ k, (A.transpose *ᵥ s.ofLp) k ^ 2 = s.ofLp ⬝ᵥ (A * A.transpose) *ᵥ s.ofLp := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
    simp [dotProduct, sq]
  rw [hq]
  congr 1
  simp [neg_div]

lemma map_pi_gaussian_linear_eval {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (A : Matrix ι κ ℝ) (i : ι) :
    (Measure.pi fun _ : κ => gaussianReal 0 1).map (fun u => (A *ᵥ u) i) =
      gaussianReal 0 ((A * A.transpose) i i).toNNReal := by
  have hPSD : (A * A.transpose).PosSemidef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose A
  have hmeas : Measurable (fun u : κ → ℝ => WithLp.toLp 2 (A *ᵥ u)) :=
    ((PiLp.continuous_toLp 2 _).comp (Continuous.matrix_mulVec continuous_const continuous_id)).measurable
  rw [show (fun u => (A *ᵥ u) i) =
      (fun v : EuclideanSpace ℝ ι => v i) ∘ (fun u => WithLp.toLp 2 (A *ᵥ u)) from rfl,
    ← Measure.map_map (PiLp.continuous_apply 2 _ i).measurable hmeas, map_pi_gaussian_linear,
    (measurePreserving_eval_multivariateGaussian hPSD).map_eq]
  simp

/-- law of a linear form of iid standard Gaussians. -/
lemma rowLaw {κ : Type*} [Fintype κ] (c : κ → ℝ) :
    (Measure.pi fun _ : κ => gaussianReal 0 1).map (fun u => ∑ q, c q * u q) =
      gaussianReal 0 (∑ q, c q ^ 2).toNNReal := by
  have h := map_pi_gaussian_linear_eval (ι := Fin 1) (Matrix.of fun (_ : Fin 1) q => c q) 0
  have e1 : (fun u : κ → ℝ => ((Matrix.of fun (_ : Fin 1) q => c q) *ᵥ u) 0) =
      fun u => ∑ q, c q * u q := by
    funext u; simp [Matrix.mulVec, dotProduct]
  have e2 : ((Matrix.of fun (_ : Fin 1) q => c q) *
      (Matrix.of fun (_ : Fin 1) q => c q).transpose) 0 0 = ∑ q, c q ^ 2 := by
    simp [Matrix.mul_apply, sq]
  rw [e1, e2] at h
  exact h

lemma lin_meas {κ : Type*} [Fintype κ] (c : κ → ℝ) :
    Measurable (fun u : κ → ℝ => ∑ q, c q * u q) := by fun_prop

lemma integral_lin {κ : Type*} [Fintype κ] (c : κ → ℝ) :
    ∫ u, ∑ q, c q * u q ∂(Measure.pi fun _ : κ => gaussianReal 0 1) = 0 := by
  have h := integral_map (μ := Measure.pi fun _ : κ => gaussianReal 0 1)
    (lin_meas c).aemeasurable (f := fun x : ℝ => x) aestronglyMeasurable_id
  rw [rowLaw, integral_id_gaussianReal] at h
  exact h.symm

lemma integral_lin_sq {κ : Type*} [Fintype κ] (c : κ → ℝ) :
    ∫ u, (∑ q, c q * u q) ^ 2 ∂(Measure.pi fun _ : κ => gaussianReal 0 1) = ∑ q, c q ^ 2 := by
  have h := integral_map (μ := Measure.pi fun _ : κ => gaussianReal 0 1)
    (lin_meas c).aemeasurable (f := fun x : ℝ => x ^ 2) (by fun_prop)
  rw [rowLaw] at h
  rw [← h]
  have hv := variance_fun_id_gaussianReal (μ := 0) (v := (∑ q, c q ^ 2).toNNReal)
  rw [variance_of_integral_eq_zero (by fun_prop) (integral_id_gaussianReal)] at hv
  rw [hv, Real.coe_toNNReal _ (Finset.sum_nonneg fun q _ => sq_nonneg _)]

lemma integrable_lin {κ : Type*} [Fintype κ] (c : κ → ℝ) :
    Integrable (fun u : κ → ℝ => ∑ q, c q * u q) (Measure.pi fun _ : κ => gaussianReal 0 1) := by
  have : Integrable (fun x : ℝ => x) ((Measure.pi fun _ : κ => gaussianReal 0 1).map
      (fun u => ∑ q, c q * u q)) := by
    rw [rowLaw]; exact (memLp_id_gaussianReal 1).integrable le_rfl
  exact this.comp_measurable (lin_meas c)

lemma isGaussian_pi (κ : Type*) [Fintype κ] :
    IsGaussian (Measure.pi fun _ : κ => gaussianReal 0 1) := by
  have h := map_pi_eq_stdGaussian (ι := κ)
  have e : (Measure.pi fun _ : κ => gaussianReal 0 1) =
      (stdGaussian (EuclideanSpace ℝ κ)).map
        (PiLp.continuousLinearEquiv 2 ℝ (fun _ : κ => ℝ)) := by
    rw [← h, Measure.map_map (by fun_prop) (by fun_prop)]
    convert (Measure.map_id).symm
    funext x; rfl
  rw [e]
  infer_instance

/-- linear processes of iid standard Gaussians are Gaussian processes. -/
lemma isGaussianProcess_lin {κ T : Type*} [Fintype κ] (a : T → κ → ℝ) :
    IsGaussianProcess (fun t (u : κ → ℝ) => ∑ q, a t q * u q)
      (Measure.pi fun _ : κ => gaussianReal 0 1) := by
  have := isGaussian_pi κ
  refine ⟨fun I => ?_⟩
  let Lm : (κ → ℝ) →ₗ[ℝ] (I → ℝ) :=
    { toFun u t := ∑ q, a t q * u q
      map_add' u v := by ext t; simp [mul_add, Finset.sum_add_distrib]
      map_smul' r u := by
        ext t; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring }
  have hfun : (fun u : κ → ℝ => I.restrict (fun t => ∑ q, a t q * u q)) =
      (LinearMap.toContinuousLinearMap Lm) := by
    funext u; ext t; rfl
  rw [hfun]
  exact (IsGaussian.hasGaussianLaw_id).map_fun _

end TG14

namespace TG14

/-- the standard Gaussian vector law on `Fin n → ℝ`. -/
noncomputable abbrev μg (n : ℕ) : Measure (Fin n → ℝ) := Measure.pi fun _ : Fin n => gaussianReal 0 1

/-- the statement of the (proved) finite-dimensional Sudakov–Fernique inequality. -/
def SFStmt : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      {ι : Type} [Fintype ι] [Nonempty ι] (X Y : ι → Ω → ℝ)
      (_hXG : IsGaussianProcess X P) (_hYG : IsGaussianProcess Y P)
      (_hXmean : ∀ i, ∫ ω, X i ω ∂P = 0) (_hYmean : ∀ i, ∫ ω, Y i ω ∂P = 0)
      (_hinc : ∀ i j, ∫ ω, (X i ω - X j ω) ^ 2 ∂P ≤ ∫ ω, (Y i ω - Y j ω) ^ 2 ∂P),
      ∫ ω, Finset.univ.sup' Finset.univ_nonempty (fun i => X i ω) ∂P ≤
        ∫ ω, Finset.univ.sup' Finset.univ_nonempty (fun i => Y i ω) ∂P

variable {n m : ℕ}

/-- adjoin the zero vector at index `none`. -/
def ext0 {J : Type} (c : J → Fin n → ℝ) : Option J → Fin n → ℝ := fun o => o.elim 0 c

@[simp] lemma ext0_none {J : Type} (c : J → Fin n → ℝ) : ext0 c none = 0 := rfl
@[simp] lemma ext0_some {J : Type} (c : J → Fin n → ℝ) (j : J) : ext0 c (some j) = c j := rfl

/-- `max(0, max_j ⟨c_j, g⟩)`. -/
def Mx {J : Type} [Fintype J] (c : J → Fin n → ℝ) (g : Fin n → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun o : Option J => ∑ k, ext0 c o k * g k)

lemma le_Mx {J : Type} [Fintype J] (c : J → Fin n → ℝ) (g : Fin n → ℝ) (o : Option J) :
    ∑ k, ext0 c o k * g k ≤ Mx c g :=
  Finset.le_sup' (f := fun o : Option J => ∑ k, ext0 c o k * g k) (Finset.mem_univ o)

lemma Mx_nonneg {J : Type} [Fintype J] (c : J → Fin n → ℝ) (g : Fin n → ℝ) : 0 ≤ Mx c g := by
  have := le_Mx c g none
  simpa using this

lemma Mx_cont {J : Type} [Fintype J] (c : J → Fin n → ℝ) : Continuous (Mx c) := by
  unfold Mx
  exact Continuous.finset_sup'_apply _ fun o _ => by fun_prop

/-- the max of finitely many linear forms of iid standard Gaussians is integrable. -/
lemma supLin_integrable {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι] (c : ι → κ → ℝ) :
    Integrable (fun u : κ → ℝ => Finset.univ.sup' Finset.univ_nonempty
      (fun i => ∑ q, c i q * u q)) (Measure.pi fun _ : κ => gaussianReal 0 1) := by
  refine Integrable.mono' (integrable_finsetSum Finset.univ fun i _ => (integrable_lin (c i)).abs)
    (Continuous.finset_sup'_apply _ fun i _ => by fun_prop).aestronglyMeasurable
    (ae_of_all _ fun u => ?_)
  rw [Real.norm_eq_abs]
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := ι))
    (fun i => ∑ q, c i q * u q)
  rw [hi]
  exact Finset.single_le_sum (f := fun i => |∑ q, c i q * u q|) (fun i _ => abs_nonneg _)
    (Finset.mem_univ i)

lemma Mx_integrable {J : Type} [Fintype J] (c : J → Fin n → ℝ) : Integrable (Mx c) (μg n) :=
  supLin_integrable (fun o => ext0 c o)

lemma neg_map : (μg n).map (fun g => -g) = μg n := by
  have : ∀ _ : Fin n, SigmaFinite ((gaussianReal 0 1).map (fun x : ℝ => -x)) := by
    intro; rw [gaussianReal_map_neg]; infer_instance
  have h := Measure.pi_map_pi (μ := fun _ : Fin n => gaussianReal 0 1) (f := fun _ (x : ℝ) => -x)
    (fun _ => measurable_neg.aemeasurable)
  simp only [gaussianReal_map_neg, neg_zero] at h
  exact h

lemma Mx_neg_integrable {J : Type} [Fintype J] (c : J → Fin n → ℝ) :
    Integrable (fun g => Mx c (-g)) (μg n) := by
  have h : Integrable (Mx c) ((μg n).map (fun g => -g)) := by rw [neg_map]; exact Mx_integrable c
  exact h.comp_measurable measurable_neg

lemma Mx_neg {J : Type} [Fintype J] (c : J → Fin n → ℝ) :
    ∫ g, Mx c (-g) ∂μg n = ∫ g, Mx c g ∂μg n := by
  have h := integral_map (μ := μg n) measurable_neg.aemeasurable (Mx_cont c).aestronglyMeasurable
  rw [neg_map] at h
  exact h.symm

lemma abs_le_Mx {J : Type} [Fintype J] (c : J → Fin n → ℝ) (j : J) (g : Fin n → ℝ) :
    |∑ k, c j k * g k| ≤ Mx c g + Mx c (-g) := by
  have h1 : ∑ k, c j k * g k ≤ Mx c g := le_Mx c g (some j)
  have h2 : -(∑ k, c j k * g k) ≤ Mx c (-g) := by
    have := le_Mx c (-g) (some j)
    simpa [Finset.sum_neg_distrib] using this
  have h3 := Mx_nonneg c g
  have h4 := Mx_nonneg c (-g)
  rcases le_total 0 (∑ k, c j k * g k) with h | h
  · rw [abs_of_nonneg h]; linarith
  · rw [abs_of_nonpos h]; linarith

/-! ### the big Gaussian space: rows indexed by `Option (Fin m)` -/

/-- row `o` of the big Gaussian matrix. -/
def row (o : Option (Fin m)) (ω : Option (Fin m) × Fin n → ℝ) : Fin n → ℝ := fun k => ω (o, k)

lemma row_mp (o : Option (Fin m)) :
    MeasurePreserving (row (n := n) o)
      (Measure.pi fun _ : Option (Fin m) × Fin n => gaussianReal 0 1) (μg n) := by
  have hc : (Measure.pi fun _ : Option (Fin m) × Fin n => gaussianReal 0 1).map
      (MeasurableEquiv.curry (Option (Fin m)) (Fin n) ℝ) =
      Measure.pi fun _ : Option (Fin m) => Measure.pi fun _ : Fin n => gaussianReal 0 1 := by
    have := Measure.infinitePi_map_curry_symm
      (fun (_ : Option (Fin m)) (_ : Fin n) => gaussianReal (0 : ℝ) 1)
    simp only [Measure.infinitePi_eq_pi] at this
    rw [MeasurableEquiv.map_apply_eq_iff_map_symm_apply_eq, this]
  have h1 : MeasurePreserving (MeasurableEquiv.curry (Option (Fin m)) (Fin n) ℝ)
      (Measure.pi fun _ : Option (Fin m) × Fin n => gaussianReal 0 1)
      (Measure.pi fun _ : Option (Fin m) => Measure.pi fun _ : Fin n => gaussianReal 0 1) :=
    ⟨(MeasurableEquiv.curry _ _ _).measurable, hc⟩
  exact (measurePreserving_eval _ o).comp h1

lemma sum_big (c : Option (Fin m) × Fin n → ℝ) (ω : Option (Fin m) × Fin n → ℝ) :
    ∑ p, c p * ω p = ∑ k, c (none, k) * ω (none, k) + ∑ i, ∑ k, c (some i, k) * ω (some i, k) := by
  rw [Fintype.sum_prod_type, Fintype.sum_option]

lemma sum_big_sq (c : Option (Fin m) × Fin n → ℝ) :
    ∑ p, c p ^ 2 = ∑ k, c (none, k) ^ 2 + ∑ i, ∑ k, c (some i, k) ^ 2 := by
  rw [Fintype.sum_prod_type, Fintype.sum_option]

/-- coefficients of the `X` process (row `none`). -/
def αc {J : Type} (a : J → Fin n → ℝ) (o : Option J) : Option (Fin m) × Fin n → ℝ :=
  fun p => p.1.elim (ext0 a o p.2) (fun _ => 0)

/-- coefficients of the `Y` process (rows `some i`). -/
def βc {J : Type} (b : J → Fin m → Fin n → ℝ) (o : Option J) : Option (Fin m) × Fin n → ℝ :=
  fun p => p.1.elim 0 (fun i => ext0 (fun j => b j i) o p.2)

lemma lin_sub {κ : Type*} [Fintype κ] (c d : κ → ℝ) (ω : κ → ℝ) :
    ∑ p, c p * ω p - ∑ p, d p * ω p = ∑ p, (c p - d p) * ω p := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

lemma ext_inc {J : Type} (a : J → Fin n → ℝ) (b : J → Fin m → Fin n → ℝ)
    (hinc : ∀ j j', ∑ k, (a j k - a j' k) ^ 2 ≤ ∑ i, ∑ k, (b j i k - b j' i k) ^ 2)
    (hzero : ∀ j, ∑ k, (a j k) ^ 2 ≤ ∑ i, ∑ k, (b j i k) ^ 2) (o o' : Option J) :
    ∑ k, (ext0 a o k - ext0 a o' k) ^ 2 ≤
      ∑ i, ∑ k, (ext0 (fun j => b j i) o k - ext0 (fun j => b j i) o' k) ^ 2 := by
  cases o with
  | none =>
    cases o' with
    | none => simp
    | some j' => simpa using hzero j'
  | some j =>
    cases o' with
    | none => simpa using hzero j
    | some j' => simpa using hinc j j'

/-- the finite Sudakov–Fernique step, real form. -/
lemma key_real (hSF : SFStmt) {J : Type} [Fintype J] (a : J → Fin n → ℝ)
    (b : J → Fin m → Fin n → ℝ)
    (hinc : ∀ j j', ∑ k, (a j k - a j' k) ^ 2 ≤ ∑ i, ∑ k, (b j i k - b j' i k) ^ 2)
    (hzero : ∀ j, ∑ k, (a j k) ^ 2 ≤ ∑ i, ∑ k, (b j i k) ^ 2) :
    ∫ g, Mx a g ∂μg n ≤ ∑ i, ∫ g, Mx (fun j => b j i) g ∂μg n := by
  set P := Measure.pi fun _ : Option (Fin m) × Fin n => gaussianReal (0 : ℝ) 1 with hP
  set X : Option J → (Option (Fin m) × Fin n → ℝ) → ℝ := fun o ω => ∑ p, αc a o p * ω p
  set Y : Option J → (Option (Fin m) × Fin n → ℝ) → ℝ := fun o ω => ∑ p, βc b o p * ω p
  have hsf := hSF P X Y (isGaussianProcess_lin _) (isGaussianProcess_lin _)
    (fun o => integral_lin _) (fun o => integral_lin _) (by
      intro o o'
      have e1 : ∀ ω, X o ω - X o' ω = ∑ p, (αc a o p - αc a o' p) * ω p :=
        fun ω => lin_sub _ _ ω
      have e2 : ∀ ω, Y o ω - Y o' ω = ∑ p, (βc b o p - βc b o' p) * ω p :=
        fun ω => lin_sub _ _ ω
      simp_rw [e1, e2]
      rw [integral_lin_sq, integral_lin_sq, sum_big_sq, sum_big_sq]
      simpa [αc, βc] using ext_inc a b hinc hzero o o')
  have hX : (fun ω => Finset.univ.sup' Finset.univ_nonempty (fun o => X o ω)) =
      fun ω => Mx a (row none ω) := by
    funext ω
    simp only [X, sum_big, Mx, row]
    simp [αc]
  have hY : ∀ ω, Finset.univ.sup' Finset.univ_nonempty (fun o => Y o ω) ≤
      ∑ i, Mx (fun j => b j i) (row (some i) ω) := by
    intro ω
    refine Finset.sup'_le _ _ fun o _ => ?_
    simp only [Y, sum_big]
    simp only [βc, Option.elim_none, zero_mul, Finset.sum_const_zero, zero_add, Option.elim_some]
    exact Finset.sum_le_sum fun i _ => le_Mx (fun j => b j i) (row (some i) ω) o
  have hrow : ∀ (o : Option (Fin m)) {J' : Type} [Fintype J'] (c : J' → Fin n → ℝ),
      ∫ ω, Mx c (row o ω) ∂P = ∫ g, Mx c g ∂μg n := by
    intro o J' _ c
    have h := integral_map (μ := P) (row_mp o).measurable.aemeasurable
      (Mx_cont c).aestronglyMeasurable
    rw [(row_mp o).map_eq] at h
    exact h.symm
  have hrowi : ∀ (o : Option (Fin m)) {J' : Type} [Fintype J'] (c : J' → Fin n → ℝ),
      Integrable (fun ω => Mx c (row o ω)) P := by
    intro o J' _ c
    have h : Integrable (Mx c) (P.map (row o)) := by
      rw [(row_mp o).map_eq]; exact Mx_integrable c
    exact h.comp_measurable (row_mp o).measurable
  calc ∫ g, Mx a g ∂μg n = ∫ ω, Finset.univ.sup' Finset.univ_nonempty (fun o => X o ω) ∂P := by
        rw [hX, hrow]
    _ ≤ ∫ ω, Finset.univ.sup' Finset.univ_nonempty (fun o => Y o ω) ∂P := hsf
    _ ≤ ∫ ω, ∑ i, Mx (fun j => b j i) (row (some i) ω) ∂P :=
        integral_mono (supLin_integrable (fun o => βc b o))
          (integrable_finsetSum _ fun i _ => hrowi _ _) hY
    _ = ∑ i, ∫ g, Mx (fun j => b j i) g ∂μg n := by
        rw [integral_finsetSum _ fun i _ => hrowi _ _]
        exact Finset.sum_congr rfl fun i _ => hrow _ _

/-- the finite Sudakov–Fernique step, in the `ℝ≥0∞` form of the empirical complexity. -/
lemma key_lintegral (hSF : SFStmt) {J : Type} [Fintype J] (a : J → Fin n → ℝ)
    (b : J → Fin m → Fin n → ℝ) (L : ℝ≥0)
    (hinc : ∀ j j', ∑ k, (a j k - a j' k) ^ 2 ≤ (L : ℝ) ^ 2 * ∑ i, ∑ k, (b j i k - b j' i k) ^ 2)
    (hzero : ∀ j, ∑ k, (a j k) ^ 2 ≤ (L : ℝ) ^ 2 * ∑ i, ∑ k, (b j i k) ^ 2) :
    ∫⁻ g, ⨆ j, ENNReal.ofReal |∑ k, a j k * g k| ∂μg n ≤
      2 * (L : ℝ≥0∞) * ∑ i, ∫⁻ g, ⨆ j, ENNReal.ofReal |∑ k, b j i k * g k| ∂μg n := by
  set b' : J → Fin m → Fin n → ℝ := fun j i k => (L : ℝ) * b j i k with hb'
  have hr := key_real hSF a b'
    (fun j j' => by
      have := hinc j j'
      simp only [b', ← mul_sub, mul_pow, ← Finset.mul_sum]
      exact this)
    (fun j => by
      have := hzero j
      simp only [b', mul_pow, ← Finset.mul_sum]
      exact this)
  have hpt : ∀ (i : Fin m) (g : Fin n → ℝ), ENNReal.ofReal (Mx (fun j => b' j i) g) ≤
      (L : ℝ≥0∞) * ⨆ j, ENNReal.ofReal |∑ k, b j i k * g k| := by
    intro i g
    obtain ⟨o, -, ho⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Option J))
      (fun o : Option J => ∑ k, ext0 (fun j => b' j i) o k * g k)
    rw [Mx, ho]
    cases o with
    | none => simp
    | some j =>
      have e : ∑ k, ext0 (fun j => b' j i) (some j) k * g k = (L : ℝ) * ∑ k, b j i k * g k := by
        simp only [ext0_some, b', Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring
      rw [e]
      calc ENNReal.ofReal ((L : ℝ) * ∑ k, b j i k * g k)
          ≤ ENNReal.ofReal ((L : ℝ) * |∑ k, b j i k * g k|) :=
            ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (le_abs_self _) L.2)
        _ = (L : ℝ≥0∞) * ENNReal.ofReal |∑ k, b j i k * g k| := by
            rw [ENNReal.ofReal_mul (NNReal.coe_nonneg L), ENNReal.ofReal_coe_nnreal]
        _ ≤ (L : ℝ≥0∞) * ⨆ j, ENNReal.ofReal |∑ k, b j i k * g k| :=
            by gcongr; exact le_iSup (fun j => ENNReal.ofReal |∑ k, b j i k * g k|) j
  have hnn : ∀ i, 0 ≤ ∫ g, Mx (fun j => b' j i) g ∂μg n :=
    fun i => integral_nonneg fun g => Mx_nonneg _ g
  calc ∫⁻ g, ⨆ j, ENNReal.ofReal |∑ k, a j k * g k| ∂μg n
      ≤ ∫⁻ g, ENNReal.ofReal (Mx a g + Mx a (-g)) ∂μg n :=
        lintegral_mono fun g => iSup_le fun j => ENNReal.ofReal_le_ofReal (abs_le_Mx a j g)
    _ = ENNReal.ofReal (∫ g, (Mx a g + Mx a (-g)) ∂μg n) :=
        (ofReal_integral_eq_lintegral_ofReal ((Mx_integrable a).add (Mx_neg_integrable a))
          (ae_of_all _ fun g => add_nonneg (Mx_nonneg a g) (Mx_nonneg a (-g)))).symm
    _ = ENNReal.ofReal (2 * ∫ g, Mx a g ∂μg n) := by
        rw [integral_add (Mx_integrable a) (Mx_neg_integrable a), Mx_neg]; ring_nf
    _ ≤ ENNReal.ofReal (2 * ∑ i, ∫ g, Mx (fun j => b' j i) g ∂μg n) :=
        ENNReal.ofReal_le_ofReal (by linarith)
    _ = 2 * ∑ i, ENNReal.ofReal (∫ g, Mx (fun j => b' j i) g ∂μg n) := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_sum_of_nonneg fun i _ => hnn i]
        simp
    _ = 2 * ∑ i, ∫⁻ g, ENNReal.ofReal (Mx (fun j => b' j i) g) ∂μg n := by
        congr 1
        exact Finset.sum_congr rfl fun i _ =>
          ofReal_integral_eq_lintegral_ofReal (Mx_integrable _) (ae_of_all _ fun g => Mx_nonneg _ g)
    _ ≤ 2 * ∑ i, (L : ℝ≥0∞) * ∫⁻ g, ⨆ j, ENNReal.ofReal |∑ k, b j i k * g k| ∂μg n := by
        gcongr with i
        rw [← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
        exact lintegral_mono fun g => hpt i g
    _ = 2 * (L : ℝ≥0∞) * ∑ i, ∫⁻ g, ⨆ j, ENNReal.ofReal |∑ k, b j i k * g k| ∂μg n := by
        simp only [Finset.mul_sum, mul_assoc]

/-- reduction of a supremum over an arbitrary set of vectors to finite subfamilies. -/
lemma sup_reduce (V : Set (Fin n → ℝ)) (C : ℝ≥0∞)
    (h : ∀ (N : ℕ) (e : ℕ → Fin n → ℝ), (∀ j, e j ∈ V) →
      ∫⁻ g, ⨆ j ∈ Finset.range N, ENNReal.ofReal |∑ k, e j k * g k| ∂μg n ≤ C) :
    ∫⁻ g, ⨆ v ∈ V, ENNReal.ofReal |∑ k, v k * g k| ∂μg n ≤ C := by
  obtain ⟨D, hDV, hDc, hVD⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace V).exists_countable_dense_subset
  rcases D.eq_empty_or_nonempty with hD | hD
  · have hV : V = ∅ := by
      rw [hD, closure_empty] at hVD; exact Set.subset_empty_iff.1 hVD
    subst hV
    simp
  obtain ⟨e, rfl⟩ := hDc.exists_eq_range hD
  set G : ℕ → (Fin n → ℝ) → ℝ≥0∞ :=
    fun N g => ⨆ j ∈ Finset.range N, ENNReal.ofReal |∑ k, e j k * g k| with hG
  have hcont : ∀ (w : Fin n → ℝ), Continuous fun g : Fin n → ℝ => ENNReal.ofReal |∑ k, w k * g k| :=
    fun w => ENNReal.continuous_ofReal.comp (continuous_abs.comp (by fun_prop))
  have hGm : ∀ N, Measurable (G N) := fun N =>
    Measurable.iSup fun j => Measurable.iSup fun _ => (hcont (e j)).measurable
  have hmono : Monotone G := fun N N' hNN g =>
    biSup_mono fun j hj => Finset.range_mono hNN hj
  have hpt : ∀ g, ⨆ v ∈ V, ENNReal.ofReal |∑ k, v k * g k| ≤ ⨆ N, G N g := by
    intro g
    refine iSup₂_le fun v hv => ?_
    have hcl : IsClosed {w : Fin n → ℝ | ENNReal.ofReal |∑ k, w k * g k| ≤ ⨆ N, G N g} :=
      isClosed_le (ENNReal.continuous_ofReal.comp (continuous_abs.comp (by fun_prop)))
        continuous_const
    have hsub : Set.range e ⊆ {w : Fin n → ℝ | ENNReal.ofReal |∑ k, w k * g k| ≤ ⨆ N, G N g} := by
      rintro _ ⟨j, rfl⟩
      show ENNReal.ofReal |∑ k, e j k * g k| ≤ ⨆ N, G N g
      refine le_iSup_of_le (j + 1) ?_
      exact le_iSup₂_of_le (f := fun i (_ : i ∈ Finset.range (j + 1)) =>
        ENNReal.ofReal |∑ k, e i k * g k|) j (Finset.mem_range.2 (Nat.lt_succ_self j)) le_rfl
    exact closure_minimal hsub hcl (hVD hv)
  calc ∫⁻ g, ⨆ v ∈ V, ENNReal.ofReal |∑ k, v k * g k| ∂μg n
      ≤ ∫⁻ g, ⨆ N, G N g ∂μg n := lintegral_mono hpt
    _ = ⨆ N, ∫⁻ g, G N g ∂μg n := lintegral_iSup hGm hmono
    _ ≤ C := iSup_le fun N => h N e fun j => hDV ⟨j, rfl⟩

lemma lip_sq {f : EuclideanSpace ℝ (Fin m) → ℝ} {L : ℝ≥0} (h : LipschitzWith L f)
    (u v : EuclideanSpace ℝ (Fin m)) :
    (f u - f v) ^ 2 ≤ (L : ℝ) ^ 2 * ∑ i, (u.ofLp i - v.ofLp i) ^ 2 := by
  have h1 := h.dist_le_mul u v
  rw [Real.dist_eq, EuclideanSpace.dist_eq] at h1
  have hs : 0 ≤ ∑ i, dist (u i) (v i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  calc (f u - f v) ^ 2 = |f u - f v| ^ 2 := (sq_abs _).symm
    _ ≤ ((L : ℝ) * √(∑ i, dist (u i) (v i) ^ 2)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
    _ = (L : ℝ) ^ 2 * ∑ i, (u.ofLp i - v.ofLp i) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hs]
        congr 1
        exact Finset.sum_congr rfl fun i _ => by rw [Real.dist_eq, sq_abs]

end TG14

open TG14 in
open RadGauss.LipschitzGaussian in
theorem main14 (hSF : SFStmt) {X Y : Type*} {m : ℕ} (F : Set (X → EuclideanSpace ℝ (Fin m)))
    (Fi : Fin m → Set (X → ℝ)) (hF : SubsetDirectSum F Fi)
    (φ : Y → EuclideanSpace ℝ (Fin m) → ℝ) (L : ℝ≥0)
    (hLip : ∀ y, LipschitzWith L (φ y)) (hzero : ∀ y, φ y 0 = 0)
    (n : ℕ) (s : Fin n → X × Y) :
    empiricalGaussian n (compClass φ F) s ≤
      2 * (L : ℝ≥0∞) * ∑ i, empiricalGaussian n (Fi i) (fun k => (s k).1) := by
  classical
  set vec : (X → EuclideanSpace ℝ (Fin m)) → Fin n → ℝ :=
    fun f k => (2 / (n : ℝ)) * φ (s k).2 (f (s k).1) with hvec
  set bv : (X → EuclideanSpace ℝ (Fin m)) → Fin m → Fin n → ℝ :=
    fun f i k => (2 / (n : ℝ)) * (f (s k).1).ofLp i with hbv
  have hsum : ∀ (c : Fin n → ℝ) (d : Fin n → Fin m → ℝ),
      (∀ k, c k ^ 2 ≤ (L : ℝ) ^ 2 * ∑ i, d k i ^ 2) →
      ∑ k, (2 / (n : ℝ) * c k) ^ 2 ≤ (L : ℝ) ^ 2 * ∑ i, ∑ k, (2 / (n : ℝ) * d k i) ^ 2 := by
    intro c d hcd
    calc ∑ k, (2 / (n : ℝ) * c k) ^ 2
        ≤ ∑ k, (2 / (n : ℝ)) ^ 2 * ((L : ℝ) ^ 2 * ∑ i, d k i ^ 2) :=
          Finset.sum_le_sum fun k _ => by
            rw [mul_pow]; exact mul_le_mul_of_nonneg_left (hcd k) (sq_nonneg _)
      _ = (L : ℝ) ^ 2 * ∑ i, ∑ k, (2 / (n : ℝ) * d k i) ^ 2 := by
          rw [Finset.sum_comm (f := fun i k => (2 / (n : ℝ) * d k i) ^ 2), Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
  have hpair : ∀ f f', ∑ k, (vec f k - vec f' k) ^ 2 ≤
      (L : ℝ) ^ 2 * ∑ i, ∑ k, (bv f i k - bv f' i k) ^ 2 := by
    intro f f'
    have := hsum (fun k => φ (s k).2 (f (s k).1) - φ (s k).2 (f' (s k).1))
      (fun k i => (f (s k).1).ofLp i - (f' (s k).1).ofLp i)
      (fun k => lip_sq (hLip (s k).2) _ _)
    simp only [vec, bv, ← mul_sub]
    exact this
  have hzero' : ∀ f, ∑ k, (vec f k) ^ 2 ≤ (L : ℝ) ^ 2 * ∑ i, ∑ k, (bv f i k) ^ 2 := by
    intro f
    have := hsum (fun k => φ (s k).2 (f (s k).1)) (fun k i => (f (s k).1).ofLp i)
      (fun k => by
        have h := lip_sq (hLip (s k).2) (f (s k).1) 0
        simpa [hzero] using h)
    simpa only [vec, bv] using this
  have step1 : empiricalGaussian n (compClass φ F) s ≤
      ∫⁻ g, ⨆ v ∈ vec '' F, ENNReal.ofReal |∑ k, v k * g k| ∂μg n := by
    unfold empiricalGaussian
    refine lintegral_mono fun g => iSup₂_le fun h hh => ?_
    obtain ⟨f, hf, rfl⟩ := hh
    refine le_iSup₂_of_le (vec f) ⟨f, hf, rfl⟩ (le_of_eq ?_)
    congr 2
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by simp only [vec]; ring
  refine step1.trans (sup_reduce _ _ fun N e he => ?_)
  choose f hfF hfe using he
  have key := key_lintegral hSF (J := ↥(Finset.range N)) (fun j => vec (f j))
    (fun j => bv (f j)) L (fun j j' => hpair _ _) (fun j => hzero' _)
  calc ∫⁻ g, ⨆ j ∈ Finset.range N, ENNReal.ofReal |∑ k, e j k * g k| ∂μg n
      ≤ ∫⁻ g, ⨆ j : ↥(Finset.range N), ENNReal.ofReal |∑ k, vec (f j) k * g k| ∂μg n := by
        refine lintegral_mono fun g => iSup₂_le fun j hj => ?_
        refine le_iSup_of_le (⟨j, hj⟩ : ↥(Finset.range N)) ?_
        rw [hfe j]
    _ ≤ 2 * (L : ℝ≥0∞) * ∑ i, ∫⁻ g, ⨆ j : ↥(Finset.range N),
          ENNReal.ofReal |∑ k, bv (f j) i k * g k| ∂μg n := key
    _ ≤ 2 * (L : ℝ≥0∞) * ∑ i, empiricalGaussian n (Fi i) (fun k => (s k).1) := by
        gcongr with i
        unfold empiricalGaussian
        refine lintegral_mono fun g => iSup_le fun j => ?_
        refine le_iSup₂_of_le (fun x => (f j x).ofLp i) (hF _ (hfF j) i) (le_of_eq ?_)
        congr 2
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by simp only [bv]; ring

open RadGauss.LipschitzGaussian in
theorem solution {X Y : Type*} {m : ℕ} (F : Set (X → EuclideanSpace ℝ (Fin m)))
    (Fi : Fin m → Set (X → ℝ)) (hF : SubsetDirectSum F Fi)
    (φ : Y → EuclideanSpace ℝ (Fin m) → ℝ) (L : ℝ≥0)
    (hLip : ∀ y, LipschitzWith L (φ y)) (hzero : ∀ y, φ y 0 = 0)
    (hbdd : ∃ M : ℝ, ∀ y a, |φ y a| ≤ M)
    (n : ℕ) (s : Fin n → X × Y) :
    empiricalGaussian n (compClass φ F) s ≤
      2 * (L : ℝ≥0∞) * ∑ i, empiricalGaussian n (Fi i) (fun k => (s k).1) := by
  have hSF : TG14.SFStmt := by
    unfold TG14.SFStmt
    intro Ω _ P _ ι _ _
    exact HighDimProb.RandomProcesses.sudakov_fernique_finite_dim P
  exact main14 hSF F Fi hF φ L hLip hzero n s
