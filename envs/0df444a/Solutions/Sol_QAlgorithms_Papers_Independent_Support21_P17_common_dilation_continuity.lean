-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P17.common_dilation_continuity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T16:56:22.149581+00:00
-- url     : https://prove2.me/submissions/d9006ea7-caf4-4aba-8e71-69af9bcc2924

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

open scoped Matrix.Norms.L2Operator MatrixOrder


lemma g71g3_sqrt_le {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (a b : A) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    CFC.sqrt a - CFC.sqrt b ≤ algebraMap ℝ A (Real.sqrt ‖a - b‖) := by
  set d := ‖a - b‖
  set t := Real.sqrt d
  have ht : 0 ≤ t := Real.sqrt_nonneg _
  have hsa : IsSelfAdjoint (a - b) := (IsSelfAdjoint.of_nonneg ha).sub (IsSelfAdjoint.of_nonneg hb)
  have h1 : a ≤ b + algebraMap ℝ A d := by
    have := hsa.le_algebraMap_norm_self
    have := add_le_add_left this b
    simpa [add_comm] using this
  set s := CFC.sqrt b
  have hs : 0 ≤ s := CFC.sqrt_nonneg b
  have hat : 0 ≤ algebraMap ℝ A t := by
    rw [Algebra.algebraMap_eq_smul_one]; exact smul_nonneg ht zero_le_one
  have hst : 0 ≤ s + algebraMap ℝ A t := add_nonneg hs hat
  have h2 : b + algebraMap ℝ A d ≤ (s + algebraMap ℝ A t) ^ 2 := by
    have hss : s * s = b := CFC.sqrt_mul_sqrt_self b hb
    have htt : algebraMap ℝ A t * algebraMap ℝ A t = algebraMap ℝ A d := by
      rw [← map_mul, Real.mul_self_sqrt (norm_nonneg _)]
    have hcomm : algebraMap ℝ A t * s = s * algebraMap ℝ A t := Algebra.commutes t s
    have : (s + algebraMap ℝ A t) ^ 2 = b + algebraMap ℝ A d + (2 * t) • s := by
      rw [sq, add_mul, mul_add, mul_add, hss, htt, hcomm, Algebra.smul_def]
      rw [map_mul, map_ofNat, mul_assoc, hcomm]; noncomm_ring
    rw [this]
    have : 0 ≤ (2 * t) • s := smul_nonneg (by positivity) hs
    exact le_add_of_nonneg_right this
  have h3 : CFC.sqrt a ≤ s + algebraMap ℝ A t := by
    calc CFC.sqrt a ≤ CFC.sqrt ((s + algebraMap ℝ A t) ^ 2) := CFC.sqrt_le_sqrt _ _ (h1.trans h2)
      _ = s + algebraMap ℝ A t := CFC.sqrt_sq _ hst
  exact sub_le_iff_le_add'.mpr h3

lemma g71g3_sqrt_sub {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (a b : A) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ‖CFC.sqrt a - CFC.sqrt b‖ ≤ Real.sqrt ‖a - b‖ := by
  have hx : IsSelfAdjoint (CFC.sqrt a - CFC.sqrt b) :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg a)).sub (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg b))
  have u := g71g3_sqrt_le a b ha hb
  have l := g71g3_sqrt_le b a hb ha
  rw [norm_sub_rev b a] at l
  have l' : -(algebraMap ℝ A (Real.sqrt ‖a - b‖)) ≤ CFC.sqrt a - CFC.sqrt b := by
    rw [neg_le, neg_sub]; exact l
  set r := Real.sqrt ‖a - b‖
  obtain (hA | hA) := subsingleton_or_nontrivial A
  · rw [Subsingleton.elim (CFC.sqrt a - CFC.sqrt b) 0, norm_zero]; exact Real.sqrt_nonneg _
  have hu := (le_algebraMap_iff_spectrum_le (R := ℝ) hx).mp u
  have hl : algebraMap ℝ A (-r) ≤ CFC.sqrt a - CFC.sqrt b := by rw [map_neg]; exact l'
  have hl2 := (algebraMap_le_iff_le_spectrum (R := ℝ) hx).mp hl
  rcases CStarAlgebra.norm_or_neg_norm_mem_spectrum hx with h | h
  · exact hu _ h
  · have := hl2 _ h; linarith

lemma g71g3_sn {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J] (A : Matrix I J ℂ) :
    specNorm A = ‖A‖ := rfl

lemma g71g3_le_of {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (A : Matrix I J ℂ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ x : J → ℂ, ∑ i, ‖(A *ᵥ x) i‖ ^ 2 ≤ C ^ 2 * ∑ j, ‖x j‖ ^ 2) : ‖A‖ ≤ C := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hC (fun x => ?_)
  refine (sq_le_sq₀ (by positivity) (by positivity)).mp ?_
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simpa using h x.ofLp

lemma g71g3_mulVec {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (A : Matrix I J ℂ) (x : J → ℂ) :
    ∑ i, ‖(A *ᵥ x) i‖ ^ 2 ≤ ‖A‖ ^ 2 * ∑ j, ‖x j‖ ^ 2 := by
  have h := Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 x)
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at h2
  simpa using h2

lemma g71g3_kron {a n m : ℕ} (K : Matrix (Fin n) (Fin m) ℂ) :
    ‖Matrix.kronecker (1 : Matrix (Fin a) (Fin a) ℂ) K‖ ≤ ‖K‖ := by
  apply g71g3_le_of _ _ (norm_nonneg _)
  intro x
  have e : ∀ q : Fin a × Fin n, (Matrix.kronecker (1 : Matrix (Fin a) (Fin a) ℂ) K *ᵥ x) q =
      (K *ᵥ (fun i => x (q.1, i))) q.2 := by
    rintro ⟨y, o⟩
    simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.one_apply, ite_mul,
      Finset.sum_ite_eq, Matrix.kronecker, Matrix.kroneckerMap_apply]
  simp_rw [e, Fintype.sum_prod_type]
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun y _ => g71g3_mulVec K _)

lemma g71g3_kronG {a : ℕ} {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (K : Matrix I J ℂ) :
    ‖Matrix.kronecker (1 : Matrix (Fin a) (Fin a) ℂ) K‖ ≤ ‖K‖ := by
  apply g71g3_le_of _ _ (norm_nonneg _)
  intro x
  have e : ∀ q : Fin a × I, (Matrix.kronecker (1 : Matrix (Fin a) (Fin a) ℂ) K *ᵥ x) q =
      (K *ᵥ (fun i => x (q.1, i))) q.2 := by
    rintro ⟨y, o⟩
    simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.one_apply, ite_mul,
      Finset.sum_ite_eq, Matrix.kronecker, Matrix.kroneckerMap_apply]
  simp_rw [e, Fintype.sum_prod_type]
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun y _ => g71g3_mulVec K _)

lemma g71g3_cs {I : Type*} [Fintype I] (w x : I → ℂ) :
    ‖star w ⬝ᵥ x‖ ^ 2 ≤ (∑ i, ‖w i‖ ^ 2) * ∑ j, ‖x j‖ ^ 2 := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 w : EuclideanSpace ℂ I) (WithLp.toLp 2 x)
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at h2
  simpa using h2

lemma g71g3_rank1 {I : Type*} [Fintype I] [DecidableEq I] (w : I → ℂ) :
    ‖Matrix.vecMulVec w (star w)‖ ≤ ∑ i, ‖w i‖ ^ 2 := by
  apply g71g3_le_of _ _ (by positivity)
  intro x
  have e : ∀ i, (Matrix.vecMulVec w (star w) *ᵥ x) i = w i * (star w ⬝ᵥ x) := by
    intro i
    simp [Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct, Finset.mul_sum, mul_assoc]
  simp_rw [e, norm_mul, mul_pow, ← Finset.sum_mul]
  calc (∑ i, ‖w i‖ ^ 2) * ‖star w ⬝ᵥ x‖ ^ 2
      ≤ (∑ i, ‖w i‖ ^ 2) * ((∑ i, ‖w i‖ ^ 2) * ∑ j, ‖x j‖ ^ 2) := by
        gcongr; exact g71g3_cs w x
    _ = _ := by ring

lemma g71g3_psd_sub {I : Type*} [Fintype I] [DecidableEq I] (F : Matrix I I ℂ) (hF : F.IsHermitian)
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
      refine (g71g3_cs x _).trans ?_
      have := g71g3_mulVec F x
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
def g71g3_ofc {I O : Type*} [DecidableEq I] (M : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) : Matrix (O × I) (O × I) ℂ :=
  Matrix.of fun p q => M (Matrix.single p.2 q.2 1) p.1 q.1

theorem g71g3_sum_psd {I ι : Type*} [Fintype I] (s : Finset ι) (A : ι → Matrix I I ℂ)
    (h : ∀ i, (A i).PosSemidef) : (∑ i ∈ s, A i).PosSemidef := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Matrix.PosSemidef.zero
  | insert a s ha ih => rw [Finset.sum_insert ha]; exact (h a).add ih

theorem g71g3_swap22 {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → ℂ) :
    ∑ i, ∑ j, ∑ m, ∑ l, f i j m l = ∑ m, ∑ l, ∑ i, ∑ j, f i j m l := by
  calc ∑ i, ∑ j, ∑ m, ∑ l, f i j m l = ∑ i, ∑ m, ∑ j, ∑ l, f i j m l :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ m, ∑ i, ∑ j, ∑ l, f i j m l := Finset.sum_comm
    _ = ∑ m, ∑ i, ∑ l, ∑ j, f i j m l :=
        Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ m, ∑ l, ∑ i, ∑ j, f i j m l := Finset.sum_congr rfl fun m _ => Finset.sum_comm

theorem g71g3_lin_expand' {I O : Type*} [Fintype I] [DecidableEq I] (M : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (X : Matrix I I ℂ) : M X = ∑ i, ∑ j, X i j • M (Matrix.single i j 1) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]

theorem g71g3_cp_of_choi {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I]
    (M : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (hC : (g71g3_ofc M).PosSemidef) :
    Entanglement.IsCompletelyPositive M := by
  intro r X hX
  obtain ⟨m1, v, hv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hX
  obtain ⟨m2, g, hg⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hC
  have hMij : ∀ i j o o', M (Matrix.single i j 1) o o' =
      ∑ l, g l (o, i) * star (g l (o', j)) := by
    intro i j o o'
    have : M (Matrix.single i j 1) o o' = g71g3_ofc M (o, i) (o', j) := rfl
    rw [this, hg, Matrix.sum_apply]
    simp [Matrix.vecMulVec_apply]
  let F : Fin m1 → Fin m2 → (Fin r × O → ℂ) := fun a l q => ∑ i, v a (q.1, i) * g l (q.2, i)
  have hY : idTensorSuperop M X = ∑ a, ∑ l, Matrix.vecMulVec (F a l) (star (F a l)) := by
    ext ⟨x, o⟩ ⟨y, o'⟩
    show M (Matrix.of fun i j => X (x, i) (y, j)) o o' = _
    rw [g71g3_lin_expand']
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, hMij, hv,
      Matrix.vecMulVec_apply, Pi.star_apply, F, star_sum, star_mul']
    simp only [Finset.sum_mul_sum]
    rw [g71g3_swap22]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun l _ =>
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hY]
  exact g71g3_sum_psd _ _ fun a => g71g3_sum_psd _ _ fun l =>
    Matrix.posSemidef_vecMulVec_self_star _

theorem g71g3_choi_of_cp {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I]
    (M : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (h : Entanglement.IsCompletelyPositive M) :
    (g71g3_ofc M).PosSemidef := by
  let e := Fintype.equivFin I
  let Ω : Fin (Fintype.card I) × I → ℂ := fun q => if q.1 = e q.2 then 1 else 0
  have hY := h _ _ (Matrix.posSemidef_vecMulVec_self_star Ω)
  have hE : g71g3_ofc M = (idTensorSuperop M (Matrix.vecMulVec Ω (star Ω))).submatrix
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



lemma g71g3_kraus {m n : ℕ} (T : Lin m n) (hT : Entanglement.IsCompletelyPositive T) :
    ∃ (r : ℕ) (G : Fin r → Matrix (Fin n) (Fin m) ℂ), ∀ (a : ℕ)
      (X : Matrix (Fin a × Fin m) (Fin a × Fin m) ℂ),
      idTensorSuperop T X = ∑ l, (Matrix.kronecker (1 : Matrix (Fin a) (Fin a) ℂ) (G l)) * X *
        (Matrix.kronecker (1 : Matrix (Fin a) (Fin a) ℂ) (G l))ᴴ := by
  obtain ⟨r, g, hg⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp (g71g3_choi_of_cp T hT)
  refine ⟨r, fun l => Matrix.of fun o i => g l (o, i), fun a X => ?_⟩
  have hMij : ∀ i j o o', T (Matrix.single i j 1) o o' = ∑ l, g l (o, i) * star (g l (o', j)) := by
    intro i j o o'
    have : T (Matrix.single i j 1) o o' = g71g3_ofc T (o, i) (o', j) := rfl
    rw [this, hg, Matrix.sum_apply]
    simp [Matrix.vecMulVec_apply]
  ext ⟨x, o⟩ ⟨y, o'⟩
  show T (Matrix.of fun i j => X (x, i) (y, j)) o o' = _
  rw [g71g3_lin_expand']
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

lemma g71g3_sub_norm {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (A : Matrix I I ℂ) (e : J ≃ I) : ‖A.submatrix e e‖ ≤ ‖A‖ := by
  apply g71g3_le_of _ _ (norm_nonneg _)
  intro x
  rw [Matrix.submatrix_mulVec_equiv]
  have h1 := g71g3_mulVec A (x ∘ e.symm)
  have h2 := Equiv.sum_comp e (fun i => ‖(A *ᵥ (x ∘ e.symm)) i‖ ^ 2)
  have h3 := Equiv.sum_comp e.symm (fun j => ‖x j‖ ^ 2)
  simp only [Function.comp_apply] at h1 h2 h3 ⊢
  rw [h2, ← h3]; exact h1

lemma g71g3_bdd {m n : ℕ} (T : Lin m n) (hT : Entanglement.IsCompletelyPositive T) :
    BddAbove {r : ℝ | ∃ (a : ℕ) (X : Matrix (Fin a × Fin m) (Fin a × Fin m) ℂ),
      specNorm X ≤ 1 ∧ r = specNorm (idTensorSuperop T X)} := by
  obtain ⟨r, G, hG⟩ := g71g3_kraus T hT
  refine ⟨∑ l, ‖G l‖ ^ 2, ?_⟩
  rintro _ ⟨a, X, hX, rfl⟩
  rw [g71g3_sn, hG a X]; rw [g71g3_sn] at hX
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  have hK := g71g3_kron (a := a) (G l)
  calc _ ≤ ‖Matrix.kronecker (1 : Matrix (Fin a) (Fin a) ℂ) (G l)‖ * ‖X‖ *
        ‖(Matrix.kronecker (1 : Matrix (Fin a) (Fin a) ℂ) (G l))ᴴ‖ :=
        (Matrix.l2_opNorm_mul _ _).trans
          (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ ‖G l‖ * 1 * ‖G l‖ := by
        rw [Matrix.l2_opNorm_conjTranspose]; gcongr
    _ = ‖G l‖ ^ 2 := by ring


set_option maxHeartbeats 1000000 in
lemma g71g3_msqrt {N : Type} [Fintype N] (a b : Matrix N N ℂ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ‖CFC.sqrt a - CFC.sqrt b‖ ≤ Real.sqrt ‖a - b‖ := g71g3_sqrt_sub a b ha hb

lemma g71g3_recon {m n : ℕ} (F : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ) (A : M m)
    (μ ν : Fin n) :
    ((tracialV m n).conjTranspose * Matrix.kronecker A F * tracialV m n) μ ν =
      ∑ a, ∑ b, (((Real.sqrt (m : ℝ))⁻¹ * (Real.sqrt (m : ℝ))⁻¹ : ℝ) : ℂ) * A a b * F (μ, a) (ν, b) := by
  simp only [Matrix.mul_apply, tracialV, Matrix.conjTranspose_apply, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Fintype.sum_prod_type]
  simp only [apply_ite, star_zero, ite_mul, zero_mul, mul_ite, mul_zero, ite_and,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  simp only [Finset.sum_mul, Complex.star_def, Complex.conj_ofReal]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  push_cast; ring

lemma g71g3_ofc_scaled {m n : ℕ} (T : Lin m n) : scaledChoi T = (m : ℂ) • g71g3_ofc T := by
  ext p q; simp [scaledChoi, g71g3_ofc]

lemma g71g3_cinv {m : ℕ} :
    (((Real.sqrt (m : ℝ))⁻¹ * (Real.sqrt (m : ℝ))⁻¹ : ℝ) : ℂ) = (m : ℂ)⁻¹ := by
  rw [← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg _)]; push_cast; rfl

lemma g71g3_dil {m n : ℕ} (hm : 0 < m) (T : Lin m n) (A : M m) :
    T A = (tracialV m n).conjTranspose * Matrix.kronecker A (scaledChoi T) * tracialV m n := by
  ext μ ν
  rw [g71g3_recon, g71g3_lin_expand' T A, g71g3_cinv]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, scaledChoi]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp

lemma g71g3_V0 (m n : ℕ) : specNorm (tracialV m n) ≤ 1 := by
  rw [g71g3_sn]
  apply g71g3_le_of _ _ zero_le_one
  intro v
  have e : ∀ x : Fin m × (Fin n × Fin m), ‖(tracialV m n *ᵥ v) x‖ ^ 2 =
      if x.1 = x.2.2 then (m : ℝ)⁻¹ * ‖v x.2.1‖ ^ 2 else 0 := by
    rintro ⟨a, μ, i⟩
    by_cases h : a = i
    · subst h
      simp [Matrix.mulVec, dotProduct, tracialV, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    · simp [Matrix.mulVec, dotProduct, tracialV, h]
  simp_rw [e]
  rw [Fintype.sum_prod_type]
  have : ∀ a : Fin m, ∑ y : Fin n × Fin m, (if a = y.2 then (m : ℝ)⁻¹ * ‖v y.1‖ ^ 2 else 0) =
      (m : ℝ)⁻¹ * ∑ μ, ‖v μ‖ ^ 2 := by
    intro a
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Finset.sum_ite_eq]; simp
  simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos m with h0 | h0
  · subst h0; simp; positivity
  · rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast h0.ne'), one_pow, one_mul]

lemma g71g3_sqrt_dil {m n : ℕ} (hm : 0 < m) (T : Lin m n) (hT : Entanglement.IsCompletelyPositive T)
    (A : M m) :
    T A = (Matrix.kronecker (1 : Matrix (Fin m) (Fin m) ℂ) (CFC.sqrt (scaledChoi T)) *
        tracialV m n).conjTranspose *
      Matrix.kronecker A (1 : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ) *
      (Matrix.kronecker (1 : Matrix (Fin m) (Fin m) ℂ) (CFC.sqrt (scaledChoi T)) * tracialV m n) := by
  have hF : (scaledChoi T).PosSemidef := by
    rw [g71g3_ofc_scaled]; exact (g71g3_choi_of_cp T hT).smul (by positivity)
  have hF0 : 0 ≤ scaledChoi T := hF.nonneg
  set R := CFC.sqrt (scaledChoi T)
  have hRs : Rᴴ = R := by
    rw [← Matrix.star_eq_conjTranspose]; exact (CFC.sqrt_nonneg _).isSelfAdjoint.star_eq
  have hRR : Rᴴ * R = scaledChoi T := by rw [hRs]; exact CFC.sqrt_mul_sqrt_self _ hF0
  have key : (Matrix.kronecker (1 : Matrix (Fin m) (Fin m) ℂ) R)ᴴ *
      Matrix.kronecker A (1 : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ) *
      Matrix.kronecker (1 : Matrix (Fin m) (Fin m) ℂ) R = Matrix.kronecker A (Rᴴ * R) := by
    unfold Matrix.kronecker
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
      ← Matrix.mul_kronecker_mul]
    simp
  rw [g71g3_dil hm T A, ← hRR, ← key, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

lemma g71g3_cb {m n : ℕ} (hm : 0 < m) (T1 T2 : Lin m n) (hT1 : Entanglement.IsCompletelyPositive T1)
    (hT2 : Entanglement.IsCompletelyPositive T2) :
    specNorm (scaledChoi T1 - scaledChoi T2) ≤ (m : ℝ) ^ 2 * matrixCBNorm (T1 - T2) := by
  have hBdd : BddAbove {r : ℝ | ∃ (a : ℕ) (X : Matrix (Fin a × Fin m) (Fin a × Fin m) ℂ),
      specNorm X ≤ 1 ∧ r = specNorm (idTensorSuperop (T1 - T2) X)} := by
    obtain ⟨B1, hB1⟩ := g71g3_bdd T1 hT1
    obtain ⟨B2, hB2⟩ := g71g3_bdd T2 hT2
    refine ⟨B1 + B2, ?_⟩
    rintro _ ⟨a, X, hX, rfl⟩
    have e : idTensorSuperop (⇑(T1 - T2)) X = idTensorSuperop T1 X - idTensorSuperop T2 X := by
      ext p q; simp [idTensorSuperop]
    rw [e, g71g3_sn]
    calc ‖idTensorSuperop T1 X - idTensorSuperop T2 X‖
        ≤ ‖idTensorSuperop T1 X‖ + ‖idTensorSuperop T2 X‖ := norm_sub_le _ _
      _ ≤ B1 + B2 := add_le_add (hB1 ⟨a, X, hX, rfl⟩) (hB2 ⟨a, X, hX, rfl⟩)
  have hD : scaledChoi T1 - scaledChoi T2 = scaledChoi (T1 - T2) := by
    ext p q; simp [scaledChoi, mul_sub]
  rw [hD]
  set D := T1 - T2
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  let ω : Fin m × Fin m → ℂ := fun q => if q.1 = q.2 then 1 else 0
  let X : Matrix (Fin m × Fin m) (Fin m × Fin m) ℂ :=
    (((m : ℝ)⁻¹ : ℝ) : ℂ) • Matrix.vecMulVec ω (star ω)
  have hω : ∑ q, ‖ω q‖ ^ 2 = m := by
    rw [Fintype.sum_prod_type]
    have : ∀ i : Fin m, ∑ j : Fin m, ‖ω (i, j)‖ ^ 2 = 1 := by
      intro i
      rw [Finset.sum_eq_single i (fun j _ hj => by simp [ω, Ne.symm hj]) (by simp)]
      simp [ω]
    simp [this]
  have hX : specNorm X ≤ 1 := by
    rw [g71g3_sn]
    calc ‖X‖ ≤ ‖(((m : ℝ)⁻¹ : ℝ) : ℂ)‖ * ‖Matrix.vecMulVec ω (star ω)‖ := norm_smul_le _ _
      _ ≤ (m : ℝ)⁻¹ * m := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hmR)]
          gcongr; rw [← hω]; exact g71g3_rank1 ω
      _ = 1 := inv_mul_cancel₀ hmR.ne'
  set Y := idTensorSuperop D X with hY
  have hYle : specNorm Y ≤ matrixCBNorm D := le_csSup hBdd ⟨m, X, hX, rfl⟩
  have hFY : scaledChoi D = ((((m : ℝ) ^ 2 : ℝ)) : ℂ) •
      Y.submatrix (Equiv.prodComm _ _) (Equiv.prodComm _ _) := by
    ext ⟨μ, a⟩ ⟨ν, b⟩
    have hblk : (Matrix.of fun i j => X (a, i) (b, j)) =
        (((m : ℝ)⁻¹ : ℝ) : ℂ) • Matrix.single a b 1 := by
      ext i j
      by_cases h1 : a = i <;> by_cases h2 : b = j
      · subst h1; subst h2; simp [X, ω, Matrix.vecMulVec_apply]
      · simp [X, ω, Matrix.vecMulVec_apply, h1, h2, Matrix.single_apply]
      · simp [X, ω, Matrix.vecMulVec_apply, h1, h2, Matrix.single_apply]
      · simp [X, ω, Matrix.vecMulVec_apply, h1, h2, Matrix.single_apply]
    rw [Matrix.smul_apply, Matrix.submatrix_apply]
    show _ = _ • D (Matrix.of fun i j => X (a, i) (b, j)) μ ν
    rw [hblk, map_smul, Matrix.smul_apply, scaledChoi]
    simp only [smul_eq_mul]
    have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    push_cast
    field_simp
  rw [hFY, g71g3_sn]
  calc ‖((((m : ℝ) ^ 2 : ℝ)) : ℂ) • Y.submatrix (Equiv.prodComm _ _) (Equiv.prodComm _ _)‖
      ≤ ‖((((m : ℝ) ^ 2 : ℝ)) : ℂ)‖ * ‖Y.submatrix (Equiv.prodComm _ _) (Equiv.prodComm _ _)‖ :=
        norm_smul_le _ _
    _ ≤ (m : ℝ) ^ 2 * ‖Y‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        gcongr; exact g71g3_sub_norm Y _
    _ ≤ (m : ℝ) ^ 2 * matrixCBNorm D := by gcongr; exact hYle

theorem solution (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (T1 T2 : Lin m n) (hT1 : Entanglement.IsCompletelyPositive T1)
    (hT2 : Entanglement.IsCompletelyPositive T2) :
    ∃ V1 V2 : Matrix (Fin m × (Fin n × Fin m)) (Fin n) ℂ,
      (∀ A, T1 A = V1.conjTranspose * Matrix.kronecker A
        (1 : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ) * V1) ∧
      (∀ A, T2 A = V2.conjTranspose * Matrix.kronecker A
        (1 : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ) * V2) ∧
      specNorm (V1 - V2) ≤ (m : ℝ) * Real.sqrt (matrixCBNorm (T1 - T2)) := by
  refine ⟨Matrix.kronecker (1 : Matrix (Fin m) (Fin m) ℂ) (CFC.sqrt (scaledChoi T1)) * tracialV m n,
    Matrix.kronecker (1 : Matrix (Fin m) (Fin m) ℂ) (CFC.sqrt (scaledChoi T2)) * tracialV m n,
    g71g3_sqrt_dil hm T1 hT1, g71g3_sqrt_dil hm T2 hT2, ?_⟩
  have hF1 : 0 ≤ scaledChoi T1 := by
    rw [g71g3_ofc_scaled]; exact ((g71g3_choi_of_cp T1 hT1).smul (by positivity)).nonneg
  have hF2 : 0 ≤ scaledChoi T2 := by
    rw [g71g3_ofc_scaled]; exact ((g71g3_choi_of_cp T2 hT2).smul (by positivity)).nonneg
  have hks : Matrix.kronecker (1 : Matrix (Fin m) (Fin m) ℂ) (CFC.sqrt (scaledChoi T1)) -
      Matrix.kronecker (1 : Matrix (Fin m) (Fin m) ℂ) (CFC.sqrt (scaledChoi T2)) =
      Matrix.kronecker (1 : Matrix (Fin m) (Fin m) ℂ)
        (CFC.sqrt (scaledChoi T1) - CFC.sqrt (scaledChoi T2)) := by
    ext p q; simp [Matrix.kronecker, mul_sub]
  rw [← Matrix.sub_mul, hks]
  have hcb := g71g3_cb hm T1 T2 hT1 hT2
  have hsq : specNorm (CFC.sqrt (scaledChoi T1) - CFC.sqrt (scaledChoi T2)) ≤
      Real.sqrt (specNorm (scaledChoi T1 - scaledChoi T2)) := g71g3_msqrt _ _ hF1 hF2
  have hc0 : 0 ≤ matrixCBNorm (T1 - T2) := by
    have : 0 ≤ specNorm (scaledChoi T1 - scaledChoi T2) := norm_nonneg _
    have hm2 : (0 : ℝ) < (m : ℝ) ^ 2 := by positivity
    nlinarith
  have h1 : specNorm (Matrix.kronecker (1 : Matrix (Fin m) (Fin m) ℂ)
      (CFC.sqrt (scaledChoi T1) - CFC.sqrt (scaledChoi T2)) * tracialV m n) ≤
      specNorm (Matrix.kronecker (1 : Matrix (Fin m) (Fin m) ℂ)
      (CFC.sqrt (scaledChoi T1) - CFC.sqrt (scaledChoi T2))) * specNorm (tracialV m n) :=
    Matrix.l2_opNorm_mul _ _
  have h2 : specNorm (Matrix.kronecker (1 : Matrix (Fin m) (Fin m) ℂ)
      (CFC.sqrt (scaledChoi T1) - CFC.sqrt (scaledChoi T2))) ≤
      specNorm (CFC.sqrt (scaledChoi T1) - CFC.sqrt (scaledChoi T2)) := g71g3_kronG _
  have h3 := g71g3_V0 m n
  have h4 : Real.sqrt (specNorm (scaledChoi T1 - scaledChoi T2)) ≤
      (m : ℝ) * Real.sqrt (matrixCBNorm (T1 - T2)) := by
    calc Real.sqrt (specNorm (scaledChoi T1 - scaledChoi T2))
        ≤ Real.sqrt ((m : ℝ) ^ 2 * matrixCBNorm (T1 - T2)) := Real.sqrt_le_sqrt hcb
      _ = (m : ℝ) * Real.sqrt (matrixCBNorm (T1 - T2)) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (Nat.cast_nonneg _)]
  have h5 : 0 ≤ specNorm (Matrix.kronecker (1 : Matrix (Fin m) (Fin m) ℂ)
      (CFC.sqrt (scaledChoi T1) - CFC.sqrt (scaledChoi T2))) := norm_nonneg _
  have h6 : 0 ≤ specNorm (tracialV m n) := norm_nonneg _
  exact h1.trans ((mul_le_mul h2 h3 h6 (h5.trans h2)).trans ((mul_one _).le.trans (hsq.trans h4)))
