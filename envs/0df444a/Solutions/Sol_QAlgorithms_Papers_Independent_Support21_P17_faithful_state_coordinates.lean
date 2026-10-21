-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P17.faithful_state_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T05:54:35.692627+00:00
-- url     : https://prove2.me/submissions/b88ad985-4e4b-491d-ba82-f86472df631c

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P17
noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix Kronecker Topology TensorProduct

open Filter

open QAlgorithms QAlgorithms.Papers.Independent.Support21.P17

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P50 (NoiseSpace completedTensorMap)

open QAlgorithms.Papers.Independent.Next46.P33 (UltraweakTest)

open QAlgorithms.Papers.Independent.Next46.P32 (PositiveKernel)

open QAlgorithms.Papers.Independent.Information100.P50 (M Lin coefficientMap)

open scoped Matrix.Norms.L2Operator

lemma g66m2_sn {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J] (A : Matrix I J ℂ) :
    specNorm A = ‖A‖ := rfl

lemma g66m2_le_of {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (A : Matrix I J ℂ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ x : J → ℂ, ∑ i, ‖(A *ᵥ x) i‖ ^ 2 ≤ C ^ 2 * ∑ j, ‖x j‖ ^ 2) : ‖A‖ ≤ C := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hC (fun x => ?_)
  refine (sq_le_sq₀ (by positivity) (by positivity)).mp ?_
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simpa using h x.ofLp

lemma g66m2_mulVec {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (A : Matrix I J ℂ) (x : J → ℂ) :
    ∑ i, ‖(A *ᵥ x) i‖ ^ 2 ≤ ‖A‖ ^ 2 * ∑ j, ‖x j‖ ^ 2 := by
  have h := Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 x)
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at h2
  simpa using h2

lemma g66m2_kron {a n m : ℕ} (K : Matrix (Fin n) (Fin m) ℂ) :
    ‖Matrix.kronecker (1 : Matrix (Fin a) (Fin a) ℂ) K‖ ≤ ‖K‖ := by
  apply g66m2_le_of _ _ (norm_nonneg _)
  intro x
  have e : ∀ q : Fin a × Fin n, (Matrix.kronecker (1 : Matrix (Fin a) (Fin a) ℂ) K *ᵥ x) q =
      (K *ᵥ (fun i => x (q.1, i))) q.2 := by
    rintro ⟨y, o⟩
    simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.one_apply, ite_mul,
      Finset.sum_ite_eq, Matrix.kronecker, Matrix.kroneckerMap_apply]
  simp_rw [e, Fintype.sum_prod_type]
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun y _ => g66m2_mulVec K _)

lemma g66m2_cs {I : Type*} [Fintype I] (w x : I → ℂ) :
    ‖star w ⬝ᵥ x‖ ^ 2 ≤ (∑ i, ‖w i‖ ^ 2) * ∑ j, ‖x j‖ ^ 2 := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 w : EuclideanSpace ℂ I) (WithLp.toLp 2 x)
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at h2
  simpa using h2

lemma g66m2_rank1 {I : Type*} [Fintype I] [DecidableEq I] (w : I → ℂ) :
    ‖Matrix.vecMulVec w (star w)‖ ≤ ∑ i, ‖w i‖ ^ 2 := by
  apply g66m2_le_of _ _ (by positivity)
  intro x
  have e : ∀ i, (Matrix.vecMulVec w (star w) *ᵥ x) i = w i * (star w ⬝ᵥ x) := by
    intro i
    simp [Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct, Finset.mul_sum, mul_assoc]
  simp_rw [e, norm_mul, mul_pow, ← Finset.sum_mul]
  calc (∑ i, ‖w i‖ ^ 2) * ‖star w ⬝ᵥ x‖ ^ 2
      ≤ (∑ i, ‖w i‖ ^ 2) * ((∑ i, ‖w i‖ ^ 2) * ∑ j, ‖x j‖ ^ 2) := by
        gcongr; exact g66m2_cs w x
    _ = _ := by ring

lemma g66m2_psd_sub {I : Type*} [Fintype I] [DecidableEq I] (F : Matrix I I ℂ) (hF : F.IsHermitian)
    (c : ℝ) (hc : ‖F‖ ≤ c) : ((c : ℂ) • (1 : Matrix I I ℂ) - F).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hF.eq]
    simp [Complex.conj_ofReal]
  · intro x
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul,
      smul_eq_mul]
    have hreal := hF.im_star_dotProduct_mulVec_self x
    have hbd : ‖star x ⬝ᵥ (F *ᵥ x)‖ ^ 2 ≤ (c * ∑ i, ‖x i‖ ^ 2) ^ 2 := by
      refine (g66m2_cs x _).trans ?_
      have := g66m2_mulVec F x
      have hc2 : ‖F‖ ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hc 2
      have hs : 0 ≤ ∑ i, ‖x i‖ ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hc2 hs]
    have hbd' : ‖star x ⬝ᵥ (F *ᵥ x)‖ ≤ c * ∑ i, ‖x i‖ ^ 2 := by
      have h0 : 0 ≤ c := (norm_nonneg _).trans hc
      exact abs_le_of_sq_le_sq' hbd (by positivity) |>.2 |> fun h => by
        simpa [abs_of_nonneg (norm_nonneg _)] using h
    have hxx : star x ⬝ᵥ x = ((∑ i, ‖x i‖ ^ 2 : ℝ) : ℂ) := by
      simp only [dotProduct, Pi.star_apply]; push_cast
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← Complex.conj_mul']; rfl
    rw [hxx, Complex.nonneg_iff]
    have hre := Complex.re_le_norm (star x ⬝ᵥ (F *ᵥ x))
    constructor
    · simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re]
      simp; linarith
    · have hreal' : (star x ⬝ᵥ (F *ᵥ x)).im = 0 := hreal
      simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
        zero_mul, add_zero, hreal', sub_zero, Complex.zero_im]
def g66m2_ofc {I O : Type*} [DecidableEq I] (M : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) : Matrix (O × I) (O × I) ℂ :=
  Matrix.of fun p q => M (Matrix.single p.2 q.2 1) p.1 q.1

theorem g66m2_sum_psd {I ι : Type*} [Fintype I] (s : Finset ι) (A : ι → Matrix I I ℂ)
    (h : ∀ i, (A i).PosSemidef) : (∑ i ∈ s, A i).PosSemidef := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Matrix.PosSemidef.zero
  | insert a s ha ih => rw [Finset.sum_insert ha]; exact (h a).add ih

theorem g66m2_swap22 {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → ℂ) :
    ∑ i, ∑ j, ∑ m, ∑ l, f i j m l = ∑ m, ∑ l, ∑ i, ∑ j, f i j m l := by
  calc ∑ i, ∑ j, ∑ m, ∑ l, f i j m l = ∑ i, ∑ m, ∑ j, ∑ l, f i j m l :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ m, ∑ i, ∑ j, ∑ l, f i j m l := Finset.sum_comm
    _ = ∑ m, ∑ i, ∑ l, ∑ j, f i j m l :=
        Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ m, ∑ l, ∑ i, ∑ j, f i j m l := Finset.sum_congr rfl fun m _ => Finset.sum_comm

theorem g66m2_lin_expand' {I O : Type*} [Fintype I] [DecidableEq I] (M : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (X : Matrix I I ℂ) : M X = ∑ i, ∑ j, X i j • M (Matrix.single i j 1) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]

theorem g66m2_cp_of_choi {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I]
    (M : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (hC : (g66m2_ofc M).PosSemidef) :
    Entanglement.IsCompletelyPositive M := by
  intro r X hX
  obtain ⟨m1, v, hv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hX
  obtain ⟨m2, g, hg⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hC
  have hMij : ∀ i j o o', M (Matrix.single i j 1) o o' =
      ∑ l, g l (o, i) * star (g l (o', j)) := by
    intro i j o o'
    have : M (Matrix.single i j 1) o o' = g66m2_ofc M (o, i) (o', j) := rfl
    rw [this, hg, Matrix.sum_apply]
    simp [Matrix.vecMulVec_apply]
  let F : Fin m1 → Fin m2 → (Fin r × O → ℂ) := fun a l q => ∑ i, v a (q.1, i) * g l (q.2, i)
  have hY : idTensorSuperop M X = ∑ a, ∑ l, Matrix.vecMulVec (F a l) (star (F a l)) := by
    ext ⟨x, o⟩ ⟨y, o'⟩
    show M (Matrix.of fun i j => X (x, i) (y, j)) o o' = _
    rw [g66m2_lin_expand']
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, hMij, hv,
      Matrix.vecMulVec_apply, Pi.star_apply, F, star_sum, star_mul']
    simp only [Finset.sum_mul_sum]
    rw [g66m2_swap22]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun l _ =>
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hY]
  exact g66m2_sum_psd _ _ fun a => g66m2_sum_psd _ _ fun l =>
    Matrix.posSemidef_vecMulVec_self_star _

theorem g66m2_choi_of_cp {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I]
    (M : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (h : Entanglement.IsCompletelyPositive M) :
    (g66m2_ofc M).PosSemidef := by
  let e := Fintype.equivFin I
  let Ω : Fin (Fintype.card I) × I → ℂ := fun q => if q.1 = e q.2 then 1 else 0
  have hY := h _ _ (Matrix.posSemidef_vecMulVec_self_star Ω)
  have hE : g66m2_ofc M = (idTensorSuperop M (Matrix.vecMulVec Ω (star Ω))).submatrix
      (fun q : O × I => (e q.2, q.1)) (fun q => (e q.2, q.1)) := by
    ext ⟨o, i⟩ ⟨o', i'⟩
    rw [Matrix.submatrix_apply]
    show M (Matrix.single i i' 1) o o' =
      M (Matrix.of fun j j' => Matrix.vecMulVec Ω (star Ω) (e i, j) (e i', j')) o o'
    have hX : (Matrix.of fun j j' => Matrix.vecMulVec Ω (star Ω) (e i, j) (e i', j')) =
        Matrix.single i i' 1 := by
      ext j j'
      by_cases h1 : i = j <;> by_cases h2 : i' = j' <;>
        simp [Matrix.single_apply, Matrix.vecMulVec_apply, Ω, h1, h2, Ne.symm, eq_comm]
    rw [hX]
  rw [hE]
  exact hY.submatrix _


lemma g66m2_coef_apply {dx dy : ℕ} (C : Fin dy → Fin dy → Fin dx → Fin dx → ℂ) (X : M dx) (y z : Fin dy) :
    coefficientMap C X y z = ∑ a, ∑ b, C y z a b * X a b := rfl

lemma g66m2_sqrt_mul {m : ℕ} (p : Fin m → ℝ) (hp : ∀ i, 0 < p i) (a b : Fin m) :
    (((Real.sqrt (p a * p b) : ℝ) : ℂ))⁻¹ =
      (((Real.sqrt (p a))⁻¹ : ℝ) : ℂ) * (((Real.sqrt (p b))⁻¹ : ℝ) : ℂ) := by
  rw [Real.sqrt_mul (hp a).le]; push_cast; rw [mul_inv]

lemma g66m2_F_eq {m n : ℕ} (p : Fin m → ℝ) (hp : ∀ i, 0 < p i) (T : Lin m n) :
    faithfulChoi p T =
      Matrix.diagonal (fun x : Fin n × Fin m => (((Real.sqrt (p x.2))⁻¹ : ℝ) : ℂ)) * g66m2_ofc T *
      Matrix.diagonal (fun x : Fin n × Fin m => (((Real.sqrt (p x.2))⁻¹ : ℝ) : ℂ)) := by
  ext x y
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, faithfulChoi, g66m2_sqrt_mul p hp]
  have e : g66m2_ofc T x y = T (Matrix.single x.2 y.2 1) x.1 y.1 := rfl
  rw [e]; ring

lemma g66m2_F_psd {m n : ℕ} (p : Fin m → ℝ) (hp : ∀ i, 0 < p i) (T : Lin m n)
    (hT : Entanglement.IsCompletelyPositive T) : (faithfulChoi p T).PosSemidef := by
  have h := (g66m2_choi_of_cp T hT).conjTranspose_mul_mul_same
    (Matrix.diagonal (fun x : Fin n × Fin m => (((Real.sqrt (p x.2))⁻¹ : ℝ) : ℂ)))
  rw [Matrix.diagonal_conjTranspose] at h
  have hs : star (fun x : Fin n × Fin m => (((Real.sqrt (p x.2))⁻¹ : ℝ) : ℂ)) =
      fun x => (((Real.sqrt (p x.2))⁻¹ : ℝ) : ℂ) := by
    funext x; simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
  rw [hs] at h
  rw [g66m2_F_eq p hp]; exact h

lemma g66m2_prep_apply {m n : ℕ} (p : Fin m → ℝ) (X : M m) (μ ν : Fin n) :
    faithfulPreparation n p X μ ν = if μ = ν then ∑ i, (p i : ℂ) * X i i else 0 := by
  rw [faithfulPreparation, g66m2_coef_apply]
  split_ifs with h
  · simp [h, ite_and]
  · simp [h]

lemma g66m2_cp_sub {m n : ℕ} (p : Fin m → ℝ) (hp : ∀ i, 0 < p i) (T : Lin m n)
    (hT : Entanglement.IsCompletelyPositive T) (c : ℝ)
    (hc : ((c : ℂ) • (1 : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ) - faithfulChoi p T).PosSemidef) :
    Entanglement.IsCompletelyPositive ((c : ℂ) • faithfulPreparation n p - T) := by
  apply g66m2_cp_of_choi
  have h := hc.conjTranspose_mul_mul_same
    (Matrix.diagonal (fun x : Fin n × Fin m => ((Real.sqrt (p x.2) : ℝ) : ℂ)))
  rw [Matrix.diagonal_conjTranspose] at h
  convert h using 1
  ext x y
  have hs : ∀ a, (Real.sqrt (p a) : ℂ) ≠ 0 := fun a => by
    exact_mod_cast (Real.sqrt_pos.mpr (hp a)).ne'
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [g66m2_ofc, Matrix.of_apply, LinearMap.sub_apply, LinearMap.smul_apply, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul, g66m2_prep_apply, Matrix.one_apply, Pi.star_apply,
    Complex.star_def, Complex.conj_ofReal, faithfulChoi, g66m2_sqrt_mul p hp]
  have hsq : ∀ a, (Real.sqrt (p a) : ℂ) * (Real.sqrt (p a) : ℂ) = (p a : ℂ) := fun a => by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hp a).le]
  obtain ⟨μ, i⟩ := x; obtain ⟨ν, j⟩ := y
  have hi : ∀ a, (Real.sqrt (p a) : ℂ) * (Real.sqrt (p a) : ℂ)⁻¹ = 1 := fun a => mul_inv_cancel₀ (hs a)
  have hj : ∀ a, (Real.sqrt (p a) : ℂ)⁻¹ * (Real.sqrt (p a) : ℂ) = 1 := fun a => inv_mul_cancel₀ (hs a)
  by_cases h1 : μ = ν <;> by_cases h2 : i = j
  · subst h1; subst h2
    simp [Matrix.single_apply]
    linear_combination (-(c : ℂ)) * hsq i + T (Matrix.single i i 1) μ μ *
      ((Real.sqrt (p i) : ℂ)⁻¹ * (Real.sqrt (p i) : ℂ) + 1) * hj i
  · subst h1
    have hz : (∑ k, if i = k ∧ j = k then (p k : ℂ) else 0) = 0 :=
      Finset.sum_eq_zero (fun k _ => if_neg (fun h => h2 (h.1.trans h.2.symm)))
    simp [h2, Matrix.single_apply, hz]
    linear_combination -(T (Matrix.single i j 1) μ μ * ((Real.sqrt (p j) : ℂ)⁻¹ * (Real.sqrt (p j) : ℂ)) * hi i
      + T (Matrix.single i j 1) μ μ * hj j)
  · subst h2
    simp [h1, Matrix.single_apply]
    linear_combination -(T (Matrix.single i i 1) μ ν * ((Real.sqrt (p i) : ℂ)⁻¹ * (Real.sqrt (p i) : ℂ)) * hi i
      + T (Matrix.single i i 1) μ ν * hj i)
  · simp [h1, h2, Matrix.single_apply]
    linear_combination -(T (Matrix.single i j 1) μ ν * ((Real.sqrt (p j) : ℂ)⁻¹ * (Real.sqrt (p j) : ℂ)) * hi i
      + T (Matrix.single i j 1) μ ν * hj j)

lemma g66m2_recon {m n : ℕ} (p : Fin m → ℝ) (F : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ) (A : M m)
    (μ ν : Fin n) :
    ((faithfulV n p).conjTranspose * Matrix.kronecker A F * faithfulV n p) μ ν =
      ∑ a, ∑ b, ((Real.sqrt (p a) * Real.sqrt (p b) : ℝ) : ℂ) * A a b * F (μ, a) (ν, b) := by
  simp only [Matrix.mul_apply, faithfulV, Matrix.conjTranspose_apply, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Fintype.sum_prod_type]
  simp only [apply_ite, star_zero, ite_mul, zero_mul, mul_ite, mul_zero, ite_and,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  simp only [Finset.sum_mul, Complex.star_def, Complex.conj_ofReal]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  push_cast; ring

lemma g66m2_kraus {m n : ℕ} (T : Lin m n) (hT : Entanglement.IsCompletelyPositive T) :
    ∃ (r : ℕ) (G : Fin r → Matrix (Fin n) (Fin m) ℂ), ∀ (a : ℕ)
      (X : Matrix (Fin a × Fin m) (Fin a × Fin m) ℂ),
      idTensorSuperop T X = ∑ l, (Matrix.kronecker (1 : Matrix (Fin a) (Fin a) ℂ) (G l)) * X *
        (Matrix.kronecker (1 : Matrix (Fin a) (Fin a) ℂ) (G l))ᴴ := by
  obtain ⟨r, g, hg⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp (g66m2_choi_of_cp T hT)
  refine ⟨r, fun l => Matrix.of fun o i => g l (o, i), fun a X => ?_⟩
  have hMij : ∀ i j o o', T (Matrix.single i j 1) o o' = ∑ l, g l (o, i) * star (g l (o', j)) := by
    intro i j o o'
    have : T (Matrix.single i j 1) o o' = g66m2_ofc T (o, i) (o', j) := rfl
    rw [this, hg, Matrix.sum_apply]
    simp [Matrix.vecMulVec_apply]
  ext ⟨x, o⟩ ⟨y, o'⟩
  show T (Matrix.of fun i j => X (x, i) (y, j)) o o' = _
  rw [g66m2_lin_expand']
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, hMij, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.kronecker, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
    Matrix.one_apply, ite_mul, one_mul, zero_mul, star_mul', apply_ite (star : ℂ → ℂ), star_one, star_zero,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_mul, Finset.mul_sum]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  conv_lhs => enter [2, x1]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => enter [2, c]; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma g66m2_sub_norm {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (A : Matrix I I ℂ) (e : J ≃ I) : ‖A.submatrix e e‖ ≤ ‖A‖ := by
  apply g66m2_le_of _ _ (norm_nonneg _)
  intro x
  rw [Matrix.submatrix_mulVec_equiv]
  have h1 := g66m2_mulVec A (x ∘ e.symm)
  have h2 := Equiv.sum_comp e (fun i => ‖(A *ᵥ (x ∘ e.symm)) i‖ ^ 2)
  have h3 := Equiv.sum_comp e.symm (fun j => ‖x j‖ ^ 2)
  simp only [Function.comp_apply] at h1 h2 h3 ⊢
  rw [h2, ← h3]; exact h1

lemma g66m2_bdd {m n : ℕ} (T : Lin m n) (hT : Entanglement.IsCompletelyPositive T) :
    BddAbove {r : ℝ | ∃ (a : ℕ) (X : Matrix (Fin a × Fin m) (Fin a × Fin m) ℂ),
      specNorm X ≤ 1 ∧ r = specNorm (idTensorSuperop T X)} := by
  obtain ⟨r, G, hG⟩ := g66m2_kraus T hT
  refine ⟨∑ l, ‖G l‖ ^ 2, ?_⟩
  rintro _ ⟨a, X, hX, rfl⟩
  rw [g66m2_sn, hG a X]; rw [g66m2_sn] at hX
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  have hK := g66m2_kron (a := a) (G l)
  calc _ ≤ ‖Matrix.kronecker (1 : Matrix (Fin a) (Fin a) ℂ) (G l)‖ * ‖X‖ *
        ‖(Matrix.kronecker (1 : Matrix (Fin a) (Fin a) ℂ) (G l))ᴴ‖ :=
        (Matrix.l2_opNorm_mul _ _).trans
          (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ ‖G l‖ * 1 * ‖G l‖ := by
        rw [Matrix.l2_opNorm_conjTranspose]; gcongr
    _ = ‖G l‖ ^ 2 := by ring

lemma g66m2_part3 {m n : ℕ} (hm : 0 < m) (p : Fin m → ℝ) (hp : ∀ i, 0 < p i)
    (hpsum : ∑ i, p i = 1) (T : Lin m n) (hT : Entanglement.IsCompletelyPositive T) :
    specNorm (faithfulChoi p T) ≤ specNorm (densityInverse p) ^ 2 * matrixCBNorm T := by
  set s : ℝ := ∑ i, (p i)⁻¹ with hs_def
  have hs : 0 < s := Finset.sum_pos (fun i _ => inv_pos.mpr (hp i)) ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  let ω : Fin m × Fin m → ℂ := fun q => if q.1 = q.2 then (((Real.sqrt (p q.1))⁻¹ : ℝ) : ℂ) else 0
  let X : Matrix (Fin m × Fin m) (Fin m × Fin m) ℂ := ((s⁻¹ : ℝ) : ℂ) • Matrix.vecMulVec ω (star ω)
  have hω : ∑ q, ‖ω q‖ ^ 2 = s := by
    rw [Fintype.sum_prod_type]; refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [ω, Ne.symm hj]) (by simp)]
    simp only [ω, if_true, Complex.norm_real, Real.norm_eq_abs, sq_abs, inv_pow]
    rw [Real.sq_sqrt (hp i).le]
  have hX : specNorm X ≤ 1 := by
    rw [g66m2_sn]
    calc ‖X‖ ≤ ‖((s⁻¹ : ℝ) : ℂ)‖ * ‖Matrix.vecMulVec ω (star ω)‖ := norm_smul_le _ _
      _ ≤ s⁻¹ * s := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs)]
          gcongr; rw [← hω]; exact g66m2_rank1 ω
      _ = 1 := inv_mul_cancel₀ hs.ne'
  set Y := idTensorSuperop T X with hY
  have hYle : specNorm Y ≤ matrixCBNorm T := by
    unfold matrixCBNorm
    exact le_csSup (g66m2_bdd T hT) ⟨m, X, hX, rfl⟩
  have hFY : faithfulChoi p T = ((s : ℝ) : ℂ) • Y.submatrix (Equiv.prodComm _ _) (Equiv.prodComm _ _) := by
    ext ⟨μ, a⟩ ⟨ν, b⟩
    have hblk : (Matrix.of fun i j => X (a, i) (b, j)) =
        ((s⁻¹ * (Real.sqrt (p a))⁻¹ * (Real.sqrt (p b))⁻¹ : ℝ) : ℂ) • Matrix.single a b 1 := by
      ext i j
      by_cases h1 : a = i <;> by_cases h2 : b = j
      · subst h1; subst h2; simp [X, ω, Matrix.vecMulVec_apply, Complex.conj_ofReal]; ring
      · simp [X, ω, Matrix.vecMulVec_apply, h1, h2, Matrix.single_apply]
      · simp [X, ω, Matrix.vecMulVec_apply, h1, h2, Matrix.single_apply]
      · simp [X, ω, Matrix.vecMulVec_apply, h1, h2, Matrix.single_apply]
    rw [Matrix.smul_apply, Matrix.submatrix_apply]
    show _ = _ • T (Matrix.of fun i j => X (a, i) (b, j)) μ ν
    rw [hblk, map_smul, Matrix.smul_apply, faithfulChoi, g66m2_sqrt_mul p hp]
    simp only [smul_eq_mul]
    push_cast
    field_simp
  -- arithmetic on the density inverse
  set N : ℝ := ‖(fun i => ((p i : ℂ))⁻¹)‖ with hN
  have hDN : specNorm (densityInverse p) = N := by
    rw [g66m2_sn, densityInverse, Matrix.l2_opNorm_diagonal]
  have hNi : ∀ i, (p i)⁻¹ ≤ N := by
    intro i
    have := norm_le_pi_norm (fun i => ((p i : ℂ))⁻¹) i
    rwa [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hp i)] at this
  have hmN : (m : ℝ) ≤ N := by
    obtain ⟨i, _, hi⟩ := Finset.exists_le_of_sum_le (s := Finset.univ) (f := p)
      (g := fun _ => (m : ℝ)⁻¹) ⟨⟨0, hm⟩, Finset.mem_univ _⟩ (by
        rw [hpsum]; simp [Finset.card_univ]; rw [mul_inv_cancel₀]; exact_mod_cast hm.ne')
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
    have h1 : (m : ℝ) * p i ≤ 1 := by
      have := mul_le_mul_of_nonneg_left hi hmpos.le
      rwa [mul_inv_cancel₀ hmpos.ne'] at this
    have h2 : p i * (p i)⁻¹ = 1 := mul_inv_cancel₀ (hp i).ne'
    have h3 := hNi i
    have h4 : 0 < (p i)⁻¹ := inv_pos.mpr (hp i)
    nlinarith
  have hsN : s ≤ m * N := by
    have := Finset.sum_le_card_nsmul Finset.univ (fun i => (p i)⁻¹) N (fun i _ => hNi i)
    simpa using this
  have hN0 : 0 ≤ N := norm_nonneg _
  have hY0 : 0 ≤ specNorm Y := norm_nonneg _
  rw [hDN, hFY, g66m2_sn]
  calc ‖((s : ℝ) : ℂ) • Y.submatrix (Equiv.prodComm _ _) (Equiv.prodComm _ _)‖
      ≤ ‖((s : ℝ) : ℂ)‖ * ‖Y.submatrix (Equiv.prodComm _ _) (Equiv.prodComm _ _)‖ := norm_smul_le _ _
    _ ≤ s * ‖Y‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
        gcongr; exact g66m2_sub_norm Y _
    _ ≤ s * matrixCBNorm T := by gcongr; exact hYle
    _ ≤ N ^ 2 * matrixCBNorm T := by
        gcongr
        · exact hY0.trans hYle
        · nlinarith

theorem solution (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (p : Fin m → ℝ) (hp : ∀ i, 0 < p i) (hpsum : ∑ i, p i = 1)
    (T : Lin m n) (hT : Entanglement.IsCompletelyPositive T) :
    (faithfulChoi p T).PosSemidef ∧
    (∃ c : ℝ, 0 < c ∧ Entanglement.IsCompletelyPositive
      ((c : ℂ) • faithfulPreparation n p - T)) ∧
    specNorm (faithfulChoi p T) ≤ specNorm (densityInverse p) ^ 2 * matrixCBNorm T ∧
    Entanglement.IsCompletelyPositive
      ((specNorm (faithfulChoi p T) : ℂ) • faithfulPreparation n p - T) ∧
    (∀ A, T A = (faithfulV n p).conjTranspose * Matrix.kronecker A (faithfulChoi p T) * faithfulV n p) ∧
    (∀ F : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ,
      (∀ A, T A = (faithfulV n p).conjTranspose * Matrix.kronecker A F * faithfulV n p) →
      F = faithfulChoi p T) := by
  have hpsd := g66m2_F_psd p hp T hT
  have hs : ∀ a, ((Real.sqrt (p a) : ℝ) : ℂ) ≠ 0 := fun a => by
    exact_mod_cast (Real.sqrt_pos.mpr (hp a)).ne'
  refine ⟨hpsd, ⟨specNorm (faithfulChoi p T) + 1, by rw [g66m2_sn]; positivity, ?_⟩,
    g66m2_part3 hm p hp hpsum T hT, ?_, ?_, ?_⟩
  · exact g66m2_cp_sub p hp T hT _ (g66m2_psd_sub _ hpsd.1 _ (by rw [← g66m2_sn]; linarith))
  · exact g66m2_cp_sub p hp T hT _ (g66m2_psd_sub _ hpsd.1 _ (by rw [← g66m2_sn]))
  · intro A
    ext μ ν
    rw [g66m2_recon, g66m2_lin_expand' T A]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, faithfulChoi, g66m2_sqrt_mul p hp]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    push_cast
    have := hs a; have := hs b
    field_simp
  · intro F hF
    ext ⟨μ, a⟩ ⟨ν, b⟩
    have h := congrFun (congrFun (hF (Matrix.single a b 1)) μ) ν
    rw [g66m2_recon] at h
    simp only [Matrix.single_apply] at h
    rw [Finset.sum_eq_single a (fun a' _ ha => by simp [Ne.symm ha]) (by simp)] at h
    rw [Finset.sum_eq_single b (fun b' _ hb => by simp [Ne.symm hb]) (by simp)] at h
    simp only [and_self, if_true, mul_one] at h
    rw [faithfulChoi, h, g66m2_sqrt_mul p hp]
    push_cast
    have := hs a; have := hs b
    field_simp

end
