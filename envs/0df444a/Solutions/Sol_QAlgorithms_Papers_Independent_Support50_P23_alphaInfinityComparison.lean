-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P23.alphaInfinityComparison
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T12:48:54.392994+00:00
-- url     : https://prove2.me/submissions/f4c3591e-73cf-4401-bb16-be5074205a26

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P23
import Mathlib

section X5mod_AI_Base
open Matrix

section X5mod_AI_Base

/-- conjugation by an isometry as a non-unital star algebra hom -/
noncomputable def x5ai_conjHom {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (W : Matrix n m ℂ) (hW : Wᴴ * W = 1) : Matrix m m ℂ →⋆ₙₐ[ℂ] Matrix n n ℂ where
  toFun X := W * X * Wᴴ
  map_smul' c X := by simp
  map_zero' := by simp
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_mul' X Y := by
    calc W * (X * Y) * Wᴴ = W * X * (Wᴴ * W) * Y * Wᴴ := by rw [hW]; simp [Matrix.mul_assoc]
      _ = _ := by simp [Matrix.mul_assoc]
  map_star' X := by simp [Matrix.star_eq_conjTranspose, conjTranspose_mul, Matrix.mul_assoc]

theorem x5ai_finite_cont {m : Type*} [Fintype m] [DecidableEq m] (M : Matrix m m ℂ) (f : ℝ → ℝ) :
    ContinuousOn f (quasispectrum ℝ M) := by
  have : (quasispectrum ℝ M).Finite := by
    rw [quasispectrum_eq_spectrum_union_zero]
    exact (M.finite_real_spectrum).union (Set.finite_singleton 0)
  exact this.continuousOn _

theorem x5ai_finite_cont' {m : Type*} [Fintype m] [DecidableEq m] (M : Matrix m m ℂ) (f : ℝ → ℝ) :
    ContinuousOn f (spectrum ℝ M) :=
  M.finite_real_spectrum.continuousOn _

theorem x5ai_conj {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (W : Matrix n m ℂ) (hW : Wᴴ * W = 1) (M : Matrix m m ℂ) (hM : M.IsHermitian)
    (f : ℝ → ℝ) (hf : f 0 = 0) : cfc f (W * M * Wᴴ) = W * cfc f M * Wᴴ := by
  have hWM : (W * M * Wᴴ).IsHermitian := by
    simp [IsHermitian, conjTranspose_mul, hM.eq, Matrix.mul_assoc]
  have hc : Continuous (x5ai_conjHom W hW) := by
    change Continuous fun X : Matrix m m ℂ => W * X * Wᴴ; fun_prop
  have h := NonUnitalStarAlgHom.map_cfcₙ (R := ℝ) (S := ℂ) (p := IsSelfAdjoint) (q := IsSelfAdjoint)
    (x5ai_conjHom W hW) f M (x5ai_finite_cont M f) hf hc hM.isSelfAdjoint hWM.isSelfAdjoint
  have h2 : W * cfcₙ f M * Wᴴ = cfcₙ f (W * M * Wᴴ) := h
  have e1 : cfcₙ f M = cfc f M := cfcₙ_eq_cfc (x5ai_finite_cont M f) hf
  have e2 : cfcₙ f (W * M * Wᴴ) = cfc f (W * M * Wᴴ) := cfcₙ_eq_cfc (x5ai_finite_cont (W * M * Wᴴ) f) hf
  rw [← e1, ← e2, h2]

/-- identity tensor X as a star algebra hom -/
noncomputable def x5ai_kronHom (C : Type*) {n : Type*} [Fintype C] [DecidableEq C] [Fintype n] [DecidableEq n] :
    Matrix n n ℂ →⋆ₐ[ℂ] Matrix (C × n) (C × n) ℂ where
  toFun X := Matrix.kronecker (1 : Matrix C C ℂ) X
  map_one' := Matrix.one_kronecker_one
  map_mul' X Y := by
    have := Matrix.mul_kronecker_mul (1 : Matrix C C ℂ) (1 : Matrix C C ℂ) X Y
    rw [Matrix.mul_one] at this
    exact this
  map_zero' := by simp
  map_add' X Y := by simp [Matrix.kronecker_add]
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one]
    ext ⟨i, j⟩ ⟨k, l⟩
    simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.smul_apply, Matrix.one_apply, Prod.mk.injEq]
    split_ifs <;> simp_all
  map_star' X := by simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker]

theorem x5ai_kron (C : Type*) {n : Type*} [Fintype C] [DecidableEq C] [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (hM : M.IsHermitian) (f : ℝ → ℝ) :
    cfc f (Matrix.kronecker (1 : Matrix C C ℂ) M) = Matrix.kronecker (1 : Matrix C C ℂ) (cfc f M) := by
  have hK : (Matrix.kronecker (1 : Matrix C C ℂ) M).IsHermitian := by
    simp [IsHermitian, Matrix.conjTranspose_kronecker, hM.eq]
  have h := StarAlgHom.map_cfc (R := ℝ) (S := ℂ) (p := IsSelfAdjoint) (q := IsSelfAdjoint)
    (x5ai_kronHom C (n := n)) f M (x5ai_finite_cont' M f)
    (by
      change Continuous fun X : Matrix n n ℂ => Matrix.kronecker (1 : Matrix C C ℂ) X
      refine continuous_pi fun i => continuous_pi fun j => ?_
      simp only [Matrix.kronecker, Matrix.kroneckerMap_apply]
      exact continuous_const.mul ((continuous_apply _).comp (continuous_apply _)))
    hM.isSelfAdjoint hK.isSelfAdjoint
  exact h.symm

end X5mod_AI_Base
end X5mod_AI_Base

section X5mod_AD_Kron
open Matrix Polynomial
open scoped ComplexOrder Kronecker

namespace X5AD
set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma aeval_diag (δ : ι → ℂ) (p : ℝ[X]) :
    aeval (diagonal δ) p = diagonal (fun k => aeval (δ k) p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq, diagonal_add]
  | monomial k c =>
    simp only [aeval_monomial, Matrix.algebraMap_eq_diagonal, diagonal_pow, diagonal_mul_diagonal]
    rfl

lemma cfc_diag (d : ι → ℝ) (f : ℝ → ℝ) :
    cfc f (diagonal (fun k => ((d k : ℝ) : ℂ))) = diagonal (fun k => ((f (d k) : ℝ) : ℂ)) := by
  set D := diagonal (fun k => ((d k : ℝ) : ℂ))
  have hfin : (spectrum ℝ D).Finite := D.finite_real_spectrum
  set s : Finset ℝ := Finset.univ.image d ∪ hfin.toFinset
  set p := Lagrange.interpolate s (fun x : ℝ => x) f
  have hp : ∀ x ∈ s, p.eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (v := fun x : ℝ => x) f (fun a _ b _ h => h) hx
  have hD : IsSelfAdjoint D := by
    rw [← Matrix.isHermitian_iff_isSelfAdjoint]
    exact isHermitian_diagonal_of_self_adjoint _ (by ext k; simp [Complex.conj_ofReal])
  have h1 : cfc f D = cfc (fun x => p.eval x) D :=
    cfc_congr fun x hx => (hp x (Finset.mem_union_right _ (hfin.mem_toFinset.2 hx))).symm
  rw [h1, cfc_polynomial p D hD, aeval_diag]
  congr 1; ext k
  rw [show ((d k : ℝ) : ℂ) = algebraMap ℝ ℂ (d k) from rfl, aeval_algebraMap_apply,
    Polynomial.aeval_def, Algebra.algebraMap_self, ← Polynomial.eval,
    hp _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ k)))]
  rfl

lemma spec {X : Matrix ι ι ℂ} (hX : X.IsHermitian) :
    X = (hX.eigenvectorUnitary : Matrix ι ι ℂ) * diagonal (fun k => ((hX.eigenvalues k : ℝ) : ℂ)) *
      (hX.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ := by
  conv_lhs => rw [← cfc_id' ℝ X hX.isSelfAdjoint]
  rw [hX.cfc_eq, IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  rfl

lemma cfc_spec {X : Matrix ι ι ℂ} (hX : X.IsHermitian) (f : ℝ → ℝ) :
    cfc f X = (hX.eigenvectorUnitary : Matrix ι ι ℂ) * diagonal (fun k => ((f (hX.eigenvalues k) : ℝ) : ℂ)) *
      (hX.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ := by
  rw [hX.cfc_eq, IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  rfl

lemma uu {X : Matrix ι ι ℂ} (hX : X.IsHermitian) :
    (hX.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ * (hX.eigenvectorUnitary : Matrix ι ι ℂ) = 1 :=
  Unitary.coe_star_mul_self _

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem cfc_kron {X : Matrix ι ι ℂ} {Y : Matrix κ κ ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (f : ℝ → ℝ) (hf0 : f 0 = 0) (hmul : ∀ x y, 0 ≤ x → 0 ≤ y → f (x * y) = f x * f y) :
    cfc f (X ⊗ₖ Y) = cfc f X ⊗ₖ cfc f Y := by
  have hXh := hX.isHermitian
  have hYh := hY.isHermitian
  set U := (hXh.eigenvectorUnitary : Matrix ι ι ℂ)
  set V := (hYh.eigenvectorUnitary : Matrix κ κ ℂ)
  set d := hXh.eigenvalues
  set e := hYh.eigenvalues
  have hW : (U ⊗ₖ V)ᴴ * (U ⊗ₖ V) = 1 := by
    rw [conjTranspose_kronecker, ← mul_kronecker_mul, uu hXh, uu hYh, one_kronecker_one]
  have hDE : diagonal (fun k => ((d k : ℝ) : ℂ)) ⊗ₖ diagonal (fun k => ((e k : ℝ) : ℂ)) =
      diagonal (fun p : ι × κ => ((d p.1 * e p.2 : ℝ) : ℂ)) := by
    rw [diagonal_kronecker_diagonal]; congr 1; ext p; simp
  have hXY : X ⊗ₖ Y = (U ⊗ₖ V) * diagonal (fun p : ι × κ => ((d p.1 * e p.2 : ℝ) : ℂ)) * (U ⊗ₖ V)ᴴ := by
    conv_lhs => rw [spec hXh, spec hYh]
    rw [← hDE, conjTranspose_kronecker, ← mul_kronecker_mul, ← mul_kronecker_mul]
  have hDh : (diagonal (fun p : ι × κ => ((d p.1 * e p.2 : ℝ) : ℂ))).IsHermitian :=
    isHermitian_diagonal_of_self_adjoint _ (by ext k; simp [Complex.conj_ofReal])
  rw [hXY, x5ai_conj (U ⊗ₖ V) hW _ hDh f hf0, cfc_diag (fun p : ι × κ => d p.1 * e p.2) f,
    cfc_spec hXh, cfc_spec hYh]
  have hd : ∀ k, 0 ≤ d k := hX.eigenvalues_nonneg
  have he : ∀ k, 0 ≤ e k := hY.eigenvalues_nonneg
  have hDE' : diagonal (fun p : ι × κ => ((f (d p.1 * e p.2) : ℝ) : ℂ)) =
      diagonal (fun k => ((f (d k) : ℝ) : ℂ)) ⊗ₖ diagonal (fun k => ((f (e k) : ℝ) : ℂ)) := by
    rw [diagonal_kronecker_diagonal]; congr 1; ext p
    simp [hmul _ _ (hd p.1) (he p.2)]
  rw [hDE', conjTranspose_kronecker, ← mul_kronecker_mul, ← mul_kronecker_mul]

end X5AD
end X5mod_AD_Kron

section X5mod_IC_Spec
open Matrix
open scoped ComplexOrder ComplexConjugate

namespace X5IC
set_option linter.unusedSectionVars false

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- operator from an orthonormal basis and real coefficients -/
noncomputable def D (b : OrthonormalBasis I ℂ (EuclideanSpace ℂ I)) (c : I → ℝ) : Matrix I I ℂ :=
  ∑ i, (c i : ℂ) • QAlgorithms.pureDensity (b i)

/-- matrix whose columns are the basis vectors -/
noncomputable def U (b : OrthonormalBasis I ℂ (EuclideanSpace ℂ I)) : Matrix I I ℂ :=
  Matrix.of fun a i => b i a

lemma inner_eq (x y : EuclideanSpace ℂ I) : inner ℂ x y = ∑ a, conj (x a) * y a := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [mul_comm]

lemma U_star_U (b : OrthonormalBasis I ℂ (EuclideanSpace ℂ I)) : (U b)ᴴ * U b = 1 := by
  ext i j
  have h := orthonormal_iff_ite.1 b.orthonormal i j
  rw [inner_eq] at h
  simp only [mul_apply, conjTranspose_apply, U, of_apply, one_apply]
  rw [← h]; rfl

lemma U_U_star (b : OrthonormalBasis I ℂ (EuclideanSpace ℂ I)) : U b * (U b)ᴴ = 1 :=
  mul_eq_one_comm.1 (U_star_U b)

lemma D_eq (b : OrthonormalBasis I ℂ (EuclideanSpace ℂ I)) (c : I → ℝ) :
    D b c = U b * diagonal (fun i => ((c i : ℝ) : ℂ)) * (U b)ᴴ := by
  ext x y
  simp only [D, Matrix.sum_apply, Matrix.smul_apply, QAlgorithms.pureDensity, of_apply, mul_apply,
    diagonal_apply, U, conjTranspose_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i (fun k _ hk => by simp [hk]) (by simp)]
  simp; ring

lemma D_herm (b : OrthonormalBasis I ℂ (EuclideanSpace ℂ I)) (c : I → ℝ) : (D b c).IsHermitian := by
  rw [D_eq]
  apply isHermitian_mul_mul_conjTranspose
  exact isHermitian_diagonal_of_self_adjoint _ (funext fun i => by simp)

lemma cfc_D (b : OrthonormalBasis I ℂ (EuclideanSpace ℂ I)) (c : I → ℝ) (f : ℝ → ℝ) (hf : f 0 = 0) :
    cfc f (D b c) = D b (fun i => f (c i)) := by
  rw [D_eq, D_eq, x5ai_conj (U b) (U_star_U b) _
    (isHermitian_diagonal_of_self_adjoint _ (funext fun i => by simp)) f hf, X5AD.cfc_diag]


lemma pd_mulVec (x : EuclideanSpace ℂ I) (v : I → ℂ) :
    QAlgorithms.pureDensity x *ᵥ v = (inner ℂ x (WithLp.toLp 2 v)) • x.ofLp := by
  ext a
  simp only [mulVec, dotProduct, QAlgorithms.pureDensity, of_apply, Pi.smul_apply, smul_eq_mul, inner_eq]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

lemma D_mulVec (b : OrthonormalBasis I ℂ (EuclideanSpace ℂ I)) (c : I → ℝ) (v : I → ℂ) :
    D b c *ᵥ v = ∑ i, ((c i : ℂ) * inner ℂ (b i) (WithLp.toLp 2 v)) • (b i).ofLp := by
  simp only [D, sum_mulVec, smul_mulVec, pd_mulVec, smul_smul]

lemma inner_D (b : OrthonormalBasis I ℂ (EuclideanSpace ℂ I)) (c : I → ℝ) (v : I → ℂ) (k : I) :
    inner ℂ (b k) (WithLp.toLp 2 (D b c *ᵥ v)) = (c k : ℂ) * inner ℂ (b k) (WithLp.toLp 2 v) := by
  rw [D_mulVec]
  have : WithLp.toLp 2 (∑ i, ((c i : ℂ) * inner ℂ (b i) (WithLp.toLp 2 v)) • (b i).ofLp) =
      ∑ i, ((c i : ℂ) * inner ℂ (b i) (WithLp.toLp 2 v)) • b i := by
    ext a; simp
  rw [this, inner_sum, Finset.sum_eq_single k]
  · rw [inner_smul_right, orthonormal_iff_ite.1 b.orthonormal k k]; simp
  · intro i _ hik; rw [inner_smul_right, orthonormal_iff_ite.1 b.orthonormal k i]; simp [Ne.symm hik]
  · simp

lemma qf_D (b : OrthonormalBasis I ℂ (EuclideanSpace ℂ I)) (c : I → ℝ) (v : I → ℂ) :
    star v ⬝ᵥ (D b c *ᵥ v) = ∑ i, ((c i * ‖inner ℂ (b i) (WithLp.toLp 2 v)‖ ^ 2 : ℝ) : ℂ) := by
  rw [D_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dotProduct_smul]
  have h : star v ⬝ᵥ (b i).ofLp = conj (inner ℂ (b i) (WithLp.toLp 2 v)) := by
    rw [inner_eq, map_sum, dotProduct]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [mul_comm]
  rw [h, smul_eq_mul, mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast; ring

lemma pd_trace (x y : EuclideanSpace ℂ I) :
    (QAlgorithms.pureDensity x * QAlgorithms.pureDensity y).trace = ((‖inner ℂ x y‖ ^ 2 : ℝ) : ℂ) := by
  have h : (QAlgorithms.pureDensity x * QAlgorithms.pureDensity y).trace =
      inner ℂ x y * conj (inner ℂ x y) := by
    simp only [trace, diag, mul_apply, QAlgorithms.pureDensity, of_apply, inner_eq, map_sum,
      Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ => ?_
    simp; ring
  rw [h, Complex.mul_conj, Complex.normSq_eq_norm_sq]

lemma tr_D_D (b b' : OrthonormalBasis I ℂ (EuclideanSpace ℂ I)) (c c' : I → ℝ) :
    (D b c * D b' c').trace = ∑ i, ∑ j, ((c i * c' j * ‖inner ℂ (b i) (b' j)‖ ^ 2 : ℝ) : ℂ) := by
  simp only [D, Finset.sum_mul, Finset.mul_sum, trace_sum, smul_mul_smul_comm, trace_smul, pd_trace,
    smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  push_cast; ring

lemma trace_D (b : OrthonormalBasis I ℂ (EuclideanSpace ℂ I)) (c : I → ℝ) :
    (D b c).trace = ∑ i, ((c i : ℝ) : ℂ) := by
  simp only [D, trace_sum, trace_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : (QAlgorithms.pureDensity (b i)).trace = 1 := by
    have h1 := orthonormal_iff_ite.1 b.orthonormal i i
    rw [inner_eq, if_pos rfl] at h1
    simp only [trace, diag, QAlgorithms.pureDensity, of_apply]
    rw [← h1]; refine Finset.sum_congr rfl fun a _ => by ring
  rw [h, mul_one]

lemma row_one (b b' : OrthonormalBasis I ℂ (EuclideanSpace ℂ I)) (i : I) :
    ∑ j, ‖inner ℂ (b i) (b' j)‖ ^ 2 = 1 := by
  rw [b'.sum_sq_norm_inner_left, b.orthonormal.1 i, one_pow]

lemma expand (b b' : OrthonormalBasis I ℂ (EuclideanSpace ℂ I)) (i : I) (v : EuclideanSpace ℂ I) :
    inner ℂ (b i) v = ∑ j, inner ℂ (b i) (b' j) * inner ℂ (b' j) v := by
  conv_lhs => rw [← b'.sum_repr' v]
  rw [inner_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_smul_right, mul_comm]

/-- support in terms of decompositions -/
lemma supp_fwd (s t : OrthonormalBasis I ℂ (EuclideanSpace ℂ I)) (ν μ : I → ℝ)
    (h : LinearMap.ker (D t μ).mulVecLin ≤ LinearMap.ker (D s ν).mulVecLin) (i j : I)
    (hij : inner ℂ (s i) (t j) ≠ 0) (hj : μ j = 0) : ν i = 0 := by
  have h1 : D t μ *ᵥ (t j).ofLp = 0 := by
    rw [D_mulVec]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k = j
    · subst hk; simp [hj]
    · rw [WithLp.toLp_ofLp, orthonormal_iff_ite.1 t.orthonormal k j, if_neg hk]; simp
  have h2 : D s ν *ᵥ (t j).ofLp = 0 := by
    have := h (show (t j).ofLp ∈ LinearMap.ker (D t μ).mulVecLin by
      rw [LinearMap.mem_ker, mulVecLin_apply, h1])
    rwa [LinearMap.mem_ker, mulVecLin_apply] at this
  have h3 := inner_D s ν (t j).ofLp i
  rw [h2, WithLp.toLp_ofLp] at h3
  simp only [WithLp.toLp_zero, inner_zero_right] at h3
  exact_mod_cast (mul_eq_zero.1 h3.symm).resolve_right hij

lemma supp_bwd (s t : OrthonormalBasis I ℂ (EuclideanSpace ℂ I)) (ν μ : I → ℝ)
    (h : ∀ i j, inner ℂ (s i) (t j) ≠ 0 → μ j = 0 → ν i = 0) :
    LinearMap.ker (D t μ).mulVecLin ≤ LinearMap.ker (D s ν).mulVecLin := by
  intro x hx
  rw [LinearMap.mem_ker, mulVecLin_apply] at hx ⊢
  have hc : ∀ j, (μ j : ℂ) * inner ℂ (t j) (WithLp.toLp 2 x) = 0 := by
    intro j; rw [← inner_D, hx]; simp
  rw [D_mulVec]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hi : ν i = 0
  · simp [hi]
  rw [expand s t i, Finset.sum_eq_zero, mul_zero, zero_smul]
  intro j _
  by_cases hij : inner ℂ (s i) (t j) = 0
  · rw [hij, zero_mul]
  · have hj : μ j ≠ 0 := fun hj => hi (h i j hij hj)
    have := hc j
    rw [mul_eq_zero] at this
    rw [this.resolve_left (by exact_mod_cast hj), mul_zero]

end X5IC
end X5mod_IC_Spec

section X5mod_IC_Layer
open MeasureTheory Set

namespace X5IC

lemma ind_int (x c : ℝ) :
    ∫⁻ u in Ioi (0 : ℝ), (Iio x).indicator (fun _ => ENNReal.ofReal c) u =
      ENNReal.ofReal c * ENNReal.ofReal x := by
  rw [lintegral_indicator_const measurableSet_Iio, Measure.restrict_apply measurableSet_Iio,
    Iio_inter_Ioi, Real.volume_Ioo, sub_zero]

lemma ind_sum {ι : Type*} [Fintype ι] (ν a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (u : ℝ) :
    ∑ i, (Iio (ν i)).indicator (fun _ => ENNReal.ofReal (a i)) u =
      ENNReal.ofReal (∑ i ∈ Finset.univ.filter (fun i => u < ν i), a i) := by
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => ha i), Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [indicator_apply, mem_Iio]

lemma lc_eq {τ : Type*} [Fintype τ] (ν a : τ → ℝ) (hν : ∀ i, 0 ≤ ν i) (ha : ∀ i, 0 ≤ a i) :
    ENNReal.ofReal (∑ i, ν i * a i) =
      ∫⁻ u in Ioi (0 : ℝ), ∑ i, (Iio (ν i)).indicator (fun _ => ENNReal.ofReal (a i)) u := by
  rw [lintegral_finsetSum _ (fun i _ => (measurable_const.indicator measurableSet_Iio)),
    ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hν i) (ha i))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ind_int, ENNReal.ofReal_mul (hν i), mul_comm]

/-- discrete layer-cake comparison -/
lemma layer {ι κ : Type*} [Fintype ι] [Fintype κ] (ν a : ι → ℝ) (μ b : κ → ℝ)
    (hν : ∀ i, 0 ≤ ν i) (ha : ∀ i, 0 ≤ a i) (hμ : ∀ j, 0 ≤ μ j) (hb : ∀ j, 0 ≤ b j)
    (h : ∀ u : ℝ, ∑ i ∈ Finset.univ.filter (fun i => u < ν i), a i ≤
      ∑ j ∈ Finset.univ.filter (fun j => u < μ j), b j) :
    ∑ i, ν i * a i ≤ ∑ j, μ j * b j := by
  have key : ENNReal.ofReal (∑ i, ν i * a i) ≤ ENNReal.ofReal (∑ j, μ j * b j) := by
    rw [lc_eq ν a hν ha, lc_eq μ b hμ hb]
    refine lintegral_mono fun u => ?_
    rw [ind_sum ν a ha, ind_sum μ b hb]
    exact ENNReal.ofReal_le_ofReal (h u)
  exact (ENNReal.ofReal_le_ofReal_iff
    (Finset.sum_nonneg fun j _ => mul_nonneg (hμ j) (hb j))).1 key

end X5IC
end X5mod_IC_Layer

section X5mod_IC_Psd
open Matrix
open scoped ComplexOrder ComplexConjugate

namespace X5IC
set_option linter.unusedSectionVars false

variable {I : Type*} [Fintype I] [DecidableEq I]

lemma smul_D (b : OrthonormalBasis I ℂ (EuclideanSpace ℂ I)) (c : I → ℝ) (L : ℝ) :
    (L : ℂ) • D b c = D b (fun i => L * c i) := by
  simp only [D, Finset.smul_sum, smul_smul]; push_cast; rfl

lemma threshold (s t : OrthonormalBasis I ℂ (EuclideanSpace ℂ I)) (ν μ : I → ℝ)
    (h : ∀ i j, inner ℂ (s i) (t j) ≠ 0 → ν i ≤ μ j) (v : EuclideanSpace ℂ I) (u : ℝ) :
    ∑ i ∈ Finset.univ.filter (fun i => u < ν i), ‖inner ℂ (s i) v‖ ^ 2 ≤
      ∑ j ∈ Finset.univ.filter (fun j => u < μ j), ‖inner ℂ (t j) v‖ ^ 2 := by
  set J := Finset.univ.filter (fun j => u < μ j)
  set w : EuclideanSpace ℂ I := ∑ j ∈ J, inner ℂ (t j) v • t j
  have hw : ∀ i, u < ν i → inner ℂ (s i) v = inner ℂ (s i) w := by
    intro i hi
    rw [expand s t i v, inner_sum, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => u < μ j)]
    rw [Finset.sum_eq_zero (s := Finset.univ.filter (fun j => ¬ u < μ j)), add_zero]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [inner_smul_right, mul_comm]
    · intro j hj
      rw [Finset.mem_filter] at hj
      by_cases h0 : inner ℂ (s i) (t j) = 0
      · rw [h0, zero_mul]
      · exact absurd (lt_of_lt_of_le hi (h i j h0)) hj.2
  have htw : ∀ j, inner ℂ (t j) w = if j ∈ J then inner ℂ (t j) v else 0 := by
    intro j
    rw [inner_sum]
    simp_rw [inner_smul_right, orthonormal_iff_ite.1 t.orthonormal j]
    simp [Finset.sum_ite_eq]
  calc ∑ i ∈ Finset.univ.filter (fun i => u < ν i), ‖inner ℂ (s i) v‖ ^ 2
      = ∑ i ∈ Finset.univ.filter (fun i => u < ν i), ‖inner ℂ (s i) w‖ ^ 2 :=
        Finset.sum_congr rfl fun i hi => by rw [hw i (Finset.mem_filter.1 hi).2]
    _ ≤ ‖w‖ ^ 2 := Orthonormal.sum_inner_products_le w s.orthonormal
    _ = ∑ j, ‖inner ℂ (t j) w‖ ^ 2 := (t.sum_sq_norm_inner_right w).symm
    _ = _ := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [htw j]; split_ifs with hj <;> simp_all [J]

lemma psd (s t : OrthonormalBasis I ℂ (EuclideanSpace ℂ I)) (ν μ : I → ℝ)
    (hν : ∀ i, 0 ≤ ν i) (hμ : ∀ j, 0 ≤ μ j) (L : ℝ) (hL : 0 ≤ L)
    (h : ∀ i j, inner ℂ (s i) (t j) ≠ 0 → ν i ≤ L * μ j) :
    ((L : ℂ) • D t μ - D s ν).PosSemidef := by
  rw [smul_D, posSemidef_iff_dotProduct_mulVec]
  refine ⟨(D_herm t _).sub (D_herm s ν), fun x => ?_⟩
  rw [sub_mulVec, dotProduct_sub, qf_D, qf_D, ← Complex.ofReal_sum, ← Complex.ofReal_sum,
    ← Complex.ofReal_sub, Complex.zero_le_real, sub_nonneg]
  exact layer ν _ (fun j => L * μ j) _ hν (fun _ => by positivity) (fun j => mul_nonneg hL (hμ j))
    (fun _ => by positivity) (threshold s t ν _ h _)

end X5IC
end X5mod_IC_Psd

section X5mod_IC_Bound

namespace X5IC

variable {I : Type*} [Fintype I]
set_option linter.unusedSectionVars false

noncomputable def T (ν μ : I → ℝ) (W : I → I → ℝ) (α : ℝ) : ℝ :=
  ∑ i, ∑ j, ν i ^ α * (if μ j = 0 then 0 else μ j ^ (1 - α)) * W i j

lemma T_upper (ν μ : I → ℝ) (W : I → I → ℝ) (M α : ℝ) (hα : 1 < α) (hM : 0 < M)
    (hν : ∀ i, 0 ≤ ν i) (hμ : ∀ j, 0 ≤ μ j) (hW : ∀ i j, 0 ≤ W i j)
    (hrow : ∀ i, ∑ j, W i j = 1) (hsum : ∑ i, ν i = 1)
    (hb : ∀ i j, W i j ≠ 0 → μ j ≠ 0 → ν i ≤ M * μ j) : T ν μ W α ≤ M ^ (α - 1) := by
  have key : ∀ i j, ν i ^ α * (if μ j = 0 then 0 else μ j ^ (1 - α)) * W i j ≤
      M ^ (α - 1) * (ν i * W i j) := by
    intro i j
    by_cases hWz : W i j = 0
    · simp [hWz]
    by_cases hμz : μ j = 0
    · simp only [hμz, if_true, mul_zero, zero_mul]
      exact mul_nonneg (Real.rpow_nonneg hM.le _) (mul_nonneg (hν i) (hW i j))
    rw [if_neg hμz]
    have hμp : 0 < μ j := lt_of_le_of_ne (hμ j) (Ne.symm hμz)
    have hle := hb i j hWz hμz
    rcases (hν i).lt_or_eq with hνp | hνz
    · have e1 : ν i ^ α = ν i * ν i ^ (α - 1) := by
        rw [← Real.rpow_one_add' (hν i) (by linarith)]; ring_nf
      have e2 : (M * μ j) ^ (α - 1) * μ j ^ (1 - α) = M ^ (α - 1) := by
        rw [Real.mul_rpow hM.le hμp.le, mul_assoc, ← Real.rpow_add hμp]; simp
      have h3 : ν i ^ (α - 1) ≤ (M * μ j) ^ (α - 1) :=
        Real.rpow_le_rpow (hν i) hle (by linarith)
      calc ν i ^ α * μ j ^ (1 - α) * W i j
          = ν i * W i j * (ν i ^ (α - 1) * μ j ^ (1 - α)) := by rw [e1]; ring
        _ ≤ ν i * W i j * ((M * μ j) ^ (α - 1) * μ j ^ (1 - α)) := by
            apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hν i) (hW i j))
            exact mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg hμp.le _)
        _ = _ := by rw [e2]; ring
    · rw [← hνz]; simp [Real.zero_rpow (show α ≠ 0 by linarith)]
  calc T ν μ W α ≤ ∑ i, ∑ j, M ^ (α - 1) * (ν i * W i j) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => key i j
    _ = M ^ (α - 1) := by
        have : ∀ i, ∑ j, M ^ (α - 1) * (ν i * W i j) = M ^ (α - 1) * ν i := fun i => by
          rw [← Finset.mul_sum, ← Finset.mul_sum, hrow, mul_one]
        rw [Finset.sum_congr rfl fun i _ => this i, ← Finset.mul_sum, hsum, mul_one]

lemma T_term_nonneg (ν μ : I → ℝ) (W : I → I → ℝ) (α : ℝ)
    (hν : ∀ i, 0 ≤ ν i) (hμ : ∀ j, 0 ≤ μ j) (hW : ∀ i j, 0 ≤ W i j) (i j : I) :
    0 ≤ ν i ^ α * (if μ j = 0 then 0 else μ j ^ (1 - α)) * W i j := by
  have : 0 ≤ (if μ j = 0 then 0 else μ j ^ (1 - α)) := by
    split_ifs
    · exact le_rfl
    · exact Real.rpow_nonneg (hμ j) _
  exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (hν i) _) this) (hW i j)

lemma T_lower (ν μ : I → ℝ) (W : I → I → ℝ) (M α : ℝ) (hM : 0 < M)
    (hν : ∀ i, 0 ≤ ν i) (hμ : ∀ j, 0 ≤ μ j) (hW : ∀ i j, 0 ≤ W i j)
    (i j : I) (hμp : 0 < μ j) (he : ν i = M * μ j) : M ^ α * (μ j * W i j) ≤ T ν μ W α := by
  have hterm : ν i ^ α * (if μ j = 0 then 0 else μ j ^ (1 - α)) * W i j = M ^ α * (μ j * W i j) := by
    rw [if_neg hμp.ne', he, Real.mul_rpow hM.le hμp.le]
    have : μ j ^ α * μ j ^ (1 - α) = μ j := by rw [← Real.rpow_add hμp]; simp
    calc M ^ α * μ j ^ α * μ j ^ (1 - α) * W i j = M ^ α * (μ j ^ α * μ j ^ (1 - α)) * W i j := by ring
      _ = _ := by rw [this]; ring
  rw [← hterm]
  unfold T
  refine le_trans ?_ (Finset.single_le_sum (fun i _ => Finset.sum_nonneg fun j _ =>
    T_term_nonneg ν μ W α hν hμ hW i j) (Finset.mem_univ i))
  exact Finset.single_le_sum (fun j _ => T_term_nonneg ν μ W α hν hμ hW i j) (Finset.mem_univ j)

/-- the comparison function q α → -log M -/
lemma q_tendsto (c L : ℝ) :
    Filter.Tendsto (fun α : ℝ => (c + α * L) / (1 - α)) Filter.atTop (nhds (-L)) := by
  have h1 : Filter.Tendsto (fun α : ℝ => 1 - α) Filter.atTop Filter.atBot := by
    exact Filter.tendsto_atTop_atBot.2 fun b => ⟨1 - b, fun a ha => by linarith⟩
  have h2 : Filter.Tendsto (fun α : ℝ => (c + L) / (1 - α)) Filter.atTop (nhds 0) :=
    Filter.Tendsto.div_atBot tendsto_const_nhds h1
  have h3 := h2.const_add (-L)
  rw [add_zero] at h3
  refine h3.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 1] with α hα
  have : (1 - α) ≠ 0 := by linarith
  field_simp; ring

end X5IC
end X5mod_IC_Bound

section X5mod_OL_Base
open Matrix
open scoped ComplexOrder

namespace X5OL

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- overlap matrix of the two eigenbases -/
noncomputable def ov {R N : Matrix I I ℂ} (hR : R.IsHermitian) (hN : N.IsHermitian) : Matrix I I ℂ :=
  star (hR.eigenvectorUnitary : Matrix I I ℂ) * (hN.eigenvectorUnitary : Matrix I I ℂ)

noncomputable def w {R N : Matrix I I ℂ} (hR : R.IsHermitian) (hN : N.IsHermitian) (i j : I) : ℝ :=
  ‖ov hR hN i j‖ ^ 2

lemma ov_unitary {R N : Matrix I I ℂ} (hR : R.IsHermitian) (hN : N.IsHermitian) :
    ov hR hN * star (ov hR hN) = 1 := by
  unfold ov
  have hU : star (hR.eigenvectorUnitary : Matrix I I ℂ) * (hR.eigenvectorUnitary : Matrix I I ℂ) = 1 :=
    Unitary.star_mul_self_of_mem (hR.eigenvectorUnitary).2
  have hV : (hN.eigenvectorUnitary : Matrix I I ℂ) * star (hN.eigenvectorUnitary : Matrix I I ℂ) = 1 :=
    Unitary.mul_star_self_of_mem (hN.eigenvectorUnitary).2
  rw [star_mul, star_star, Matrix.mul_assoc, ← Matrix.mul_assoc (hN.eigenvectorUnitary : Matrix I I ℂ),
    hV, Matrix.one_mul, hU]

lemma w_row {R N : Matrix I I ℂ} (hR : R.IsHermitian) (hN : N.IsHermitian) (i : I) :
    ∑ j, w hR hN i j = 1 := by
  have h := congrFun (congrFun (ov_unitary hR hN) i) i
  rw [mul_apply, one_apply_eq] at h
  have : (∑ j, ((w hR hN i j : ℝ) : ℂ)) = 1 := by
    rw [← h]; refine Finset.sum_congr rfl fun j _ => ?_
    simp only [w, star_apply, Complex.ofReal_pow]
    rw [RCLike.star_def, Complex.mul_conj']
  exact_mod_cast this

lemma w_nonneg {R N : Matrix I I ℂ} (hR : R.IsHermitian) (hN : N.IsHermitian) (i j : I) :
    0 ≤ w hR hN i j := by unfold w; positivity

lemma tr_cfc_cfc {R N : Matrix I I ℂ} (hR : R.IsHermitian) (hN : N.IsHermitian) (f g : ℝ → ℝ) :
    (cfc f R * cfc g N).trace =
      ∑ i, ∑ j, ((f (hR.eigenvalues i) * g (hN.eigenvalues j) * w hR hN i j : ℝ) : ℂ) := by
  rw [hR.cfc_eq, hN.cfc_eq]
  unfold IsHermitian.cfc
  simp only [Unitary.conjStarAlgAut_apply]
  set U := (hR.eigenvectorUnitary : Matrix I I ℂ)
  set V := (hN.eigenvectorUnitary : Matrix I I ℂ)
  set Df := diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ f ∘ hR.eigenvalues)
  set Dg := diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ g ∘ hN.eigenvalues)
  have hU : star U * U = 1 := Unitary.star_mul_self_of_mem (hR.eigenvectorUnitary).2
  have hU' : U * star U = 1 := Unitary.mul_star_self_of_mem (hR.eigenvectorUnitary).2
  have : (U * Df * star U * (V * Dg * star V)).trace = (Df * (star U * V) * Dg * star (star U * V)).trace := by
    rw [star_mul, star_star]
    rw [show U * Df * star U * (V * Dg * star V) = U * (Df * (star U * V) * Dg * (star V * U)) * star U by
      simp only [Matrix.mul_assoc]; rw [hU']; simp]
    rw [Matrix.trace_mul_cycle, hU, Matrix.one_mul]
  rw [this]
  change (Df * ov hR hN * Dg * star (ov hR hN)).trace = _
  have hE : ∀ i k, (Df * ov hR hN * Dg) i k =
      ((f (hR.eigenvalues i) : ℝ) : ℂ) * ov hR hN i k * ((g (hN.eigenvalues k) : ℝ) : ℂ) := by
    intro i k; simp [Df, Dg, diagonal_mul, mul_diagonal]
  simp only [Matrix.trace, diag_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hE, star_apply]
  simp only [w, Complex.ofReal_mul, Complex.ofReal_pow]
  rw [← Complex.mul_conj', RCLike.star_def]
  ring

lemma ov_apply {R N : Matrix I I ℂ} (hR : R.IsHermitian) (hN : N.IsHermitian) (i j : I) :
    ov hR hN i j = star (hR.eigenvectorBasis i).ofLp ⬝ᵥ (hN.eigenvectorBasis j).ofLp := by
  simp only [ov, mul_apply, star_apply, IsHermitian.eigenvectorUnitary_apply, dotProduct, Pi.star_apply]

lemma supp_fwd {R N : Matrix I I ℂ} (hR : R.IsHermitian) (hN : N.IsHermitian)
    (h : LinearMap.ker N.mulVecLin ≤ LinearMap.ker R.mulVecLin) (i j : I)
    (hi : hR.eigenvalues i ≠ 0) (hj : hN.eigenvalues j = 0) : ov hR hN i j = 0 := by
  set b := (hR.eigenvectorBasis i).ofLp
  set v := (hN.eigenvectorBasis j).ofLp
  have hNv : N *ᵥ v = 0 := by rw [hN.mulVec_eigenvectorBasis j, hj, zero_smul]
  have hRv : R *ᵥ v = 0 := by
    have := h (show v ∈ LinearMap.ker N.mulVecLin by rw [LinearMap.mem_ker, mulVecLin_apply]; exact hNv)
    rwa [LinearMap.mem_ker, mulVecLin_apply] at this
  have key : ((hR.eigenvalues i : ℝ) : ℂ) * (star b ⬝ᵥ v) = 0 := by
    have hb : R *ᵥ b = hR.eigenvalues i • b := hR.mulVec_eigenvectorBasis i
    have : star (R *ᵥ b) ⬝ᵥ v = star b ⬝ᵥ (R *ᵥ v) := by
      rw [star_mulVec, hR.eq, dotProduct_mulVec]
    rw [hRv, dotProduct_zero, hb, star_smul] at this
    rw [← this, smul_dotProduct]
    simp [RCLike.real_smul_eq_coe_mul]
  rw [ov_apply]
  rcases mul_eq_zero.1 key with h1 | h1
  · exact absurd (by exact_mod_cast h1) hi
  · exact h1

lemma spec_mulVec {R : Matrix I I ℂ} (hR : R.IsHermitian) (x : I → ℂ) :
    R *ᵥ x = (hR.eigenvectorUnitary : Matrix I I ℂ) *ᵥ
      (diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ hR.eigenvalues) *ᵥ (star (hR.eigenvectorUnitary : Matrix I I ℂ) *ᵥ x)) := by
  conv_lhs => rw [hR.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply, ← mulVec_mulVec, ← mulVec_mulVec]

lemma supp_bwd {R N : Matrix I I ℂ} (hR : R.IsHermitian) (hN : N.IsHermitian)
    (h : ∀ i j, hR.eigenvalues i ≠ 0 → hN.eigenvalues j = 0 → ov hR hN i j = 0) :
    LinearMap.ker N.mulVecLin ≤ LinearMap.ker R.mulVecLin := by
  intro x hx
  rw [LinearMap.mem_ker, mulVecLin_apply] at hx ⊢
  set U := (hR.eigenvectorUnitary : Matrix I I ℂ)
  set V := (hN.eigenvectorUnitary : Matrix I I ℂ)
  have hV : V * star V = 1 := Unitary.mul_star_self_of_mem (hN.eigenvectorUnitary).2
  have hV' : star V * V = 1 := Unitary.star_mul_self_of_mem (hN.eigenvectorUnitary).2
  set c := star V *ᵥ x
  have hc : ∀ j, hN.eigenvalues j ≠ 0 → c j = 0 := by
    intro j hj
    have h1 : star V *ᵥ (N *ᵥ x) = 0 := by rw [hx, mulVec_zero]
    rw [spec_mulVec hN, mulVec_mulVec, hV', one_mulVec] at h1
    have := congrFun h1 j
    rw [mulVec_diagonal] at this
    simp only [Function.comp_apply, Pi.zero_apply] at this
    rcases mul_eq_zero.1 this with h2 | h2
    · exact absurd (by simpa using h2) hj
    · exact h2
  have hUx : star U *ᵥ x = ov hR hN *ᵥ c := by
    rw [show ov hR hN = star U * V from rfl, mulVec_mulVec, Matrix.mul_assoc, hV, Matrix.mul_one]
  have hD : diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ hR.eigenvalues) *ᵥ (star U *ᵥ x) = 0 := by
    ext i
    rw [hUx, mulVec_diagonal, Pi.zero_apply]
    by_cases hi : hR.eigenvalues i = 0
    · simp [hi]
    · simp only [mulVec, dotProduct]
      rw [Finset.sum_eq_zero, mul_zero]
      intro j _
      by_cases hj : hN.eigenvalues j = 0
      · rw [h i j hi hj, zero_mul]
      · rw [hc j hj, mul_zero]
  rw [spec_mulVec hR, hD, mulVec_zero]

end X5OL
end X5mod_OL_Base

section X5mod_OL_Main
open Matrix Filter
open scoped ComplexOrder Topology

namespace X5OL

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- the scalar function behind tr(ρ^α N^{1-α}) -/
noncomputable def Φ (ν μ : I → ℝ) (W : I → I → ℝ) (α : ℝ) : ℝ :=
  ∑ i, ∑ j, if 0 < ν i ∧ 0 < μ j then W i j * Real.exp (α * Real.log (ν i) + (1 - α) * Real.log (μ j)) else 0

noncomputable def Φ' (ν μ : I → ℝ) (W : I → I → ℝ) : ℝ :=
  ∑ i, ∑ j, if 0 < ν i ∧ 0 < μ j then W i j * ν i * (Real.log (ν i) - Real.log (μ j)) else 0

lemma Φ_deriv (ν μ : I → ℝ) (W : I → I → ℝ) : HasDerivAt (Φ ν μ W) (Φ' ν μ W) 1 := by
  unfold Φ Φ'
  refine HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ => ?_
  split_ifs with h
  · have h1 : HasDerivAt (fun α : ℝ => α * Real.log (ν i) + (1 - α) * Real.log (μ j))
        (Real.log (ν i) - Real.log (μ j)) 1 := by
      have := ((hasDerivAt_id (1 : ℝ)).mul_const (Real.log (ν i))).add
        (((hasDerivAt_const (1 : ℝ) (1 : ℝ)).sub (hasDerivAt_id (1 : ℝ))).mul_const (Real.log (μ j)))
      exact this.congr_deriv (by ring)
    have h2 := (h1.exp).const_mul (W i j)
    refine h2.congr_deriv ?_
    simp only [one_mul, sub_self, zero_mul, add_zero, Real.exp_log h.1]
    ring
  · exact hasDerivAt_const _ _

lemma Φ_cont (ν μ : I → ℝ) (W : I → I → ℝ) : Continuous (Φ ν μ W) := by
  unfold Φ
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  split_ifs
  · fun_prop
  · exact continuous_const

lemma Φ_one (ν μ : I → ℝ) (W : I → I → ℝ) :
    Φ ν μ W 1 = ∑ i, ∑ j, if 0 < ν i ∧ 0 < μ j then W i j * ν i else 0 := by
  unfold Φ
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h
  · simp [Real.exp_log h.1]
  · rfl

lemma tr_alpha {R N : Matrix I I ℂ} (hR : R.IsHermitian) (hN : N.IsHermitian)
    (hR0 : ∀ i, 0 ≤ hR.eigenvalues i) (hN0 : ∀ j, 0 ≤ hN.eigenvalues j) (α : ℝ) (hα : 0 < α) :
    (cfc (fun x : ℝ => x ^ α) R * cfc (fun x : ℝ => if x = 0 then 0 else x ^ (1 - α)) N).trace.re =
      Φ hR.eigenvalues hN.eigenvalues (w hR hN) α := by
  rw [tr_cfc_cfc hR hN, Complex.re_sum]
  unfold Φ
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.ofReal_re]
  rcases (hR0 i).lt_or_eq with hi | hi
  · rcases (hN0 j).lt_or_eq with hj | hj
    · rw [if_neg hj.ne', if_pos ⟨hi, hj⟩, Real.rpow_def_of_pos hi, Real.rpow_def_of_pos hj, ← Real.exp_add]
      ring_nf
    · rw [← hj]; simp
  · rw [← hi]; simp [Real.zero_rpow hα.ne']

section scalar
variable (ν μ : I → ℝ) (W : I → I → ℝ) (hν : ∀ i, 0 ≤ ν i) (hμ : ∀ j, 0 ≤ μ j)
  (hW : ∀ i j, 0 ≤ W i j) (hrow : ∀ i, ∑ j, W i j = 1)
include hν hμ hrow

lemma Φ_one_supp (hs : ∀ i j, ν i ≠ 0 → μ j = 0 → W i j = 0) : Φ ν μ W 1 = ∑ i, ν i := by
  rw [Φ_one]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine (Finset.sum_congr rfl fun j _ => ?_).trans
    (show ∑ j, ν i * W i j = ν i by rw [← Finset.mul_sum, hrow, mul_one])
  rcases (hν i).lt_or_eq with hi | hi
  · rcases (hμ j).lt_or_eq with hj | hj
    · rw [if_pos ⟨hi, hj⟩]; ring
    · rw [if_neg (fun h => h.2.ne hj), hs i j hi.ne' hj.symm, mul_zero]
  · rw [if_neg (fun h => h.1.ne hi), ← hi, zero_mul]

lemma value_supp (hs : ∀ i j, ν i ≠ 0 → μ j = 0 → W i j = 0) :
    (∑ i, ∑ j, ν i * Real.logb 2 (μ j) * W i j) + -∑ i, ν i * Real.logb 2 (ν i) =
      -Φ' ν μ W / Real.log 2 := by
  unfold Φ'
  rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show ν i * Real.logb 2 (ν i) = ∑ j, ν i * Real.logb 2 (ν i) * W i j by
      rw [← Finset.mul_sum, hrow, mul_one]]
  rw [Finset.sum_div, ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rcases (hν i).lt_or_eq with hi | hi
  · rcases (hμ j).lt_or_eq with hj | hj
    · rw [if_pos ⟨hi, hj⟩]; unfold Real.logb; ring
    · rw [if_neg (fun h => h.2.ne hj), hs i j hi.ne' hj.symm]; simp
  · rw [if_neg (fun h => h.1.ne hi), ← hi]; simp

include hW in
lemma Φ_one_lt (hex : ∃ i j, ν i ≠ 0 ∧ μ j = 0 ∧ W i j ≠ 0) : Φ ν μ W 1 < ∑ i, ν i := by
  obtain ⟨i0, j0, hi0, hj0, hw0⟩ := hex
  rw [Φ_one]
  have hle : ∀ i j, (if 0 < ν i ∧ 0 < μ j then W i j * ν i else 0) ≤ W i j * ν i := by
    intro i j; split_ifs
    · exact le_rfl
    · exact mul_nonneg (hW i j) (hν i)
  refine Finset.sum_lt_sum (fun i _ => ?_) ⟨i0, Finset.mem_univ _, ?_⟩
  · calc _ ≤ ∑ j, W i j * ν i := Finset.sum_le_sum fun j _ => hle i j
      _ = ν i := by rw [← Finset.sum_mul, hrow, one_mul]
  · calc _ < ∑ j, W i0 j * ν i0 := by
          refine Finset.sum_lt_sum (fun j _ => hle i0 j) ⟨j0, Finset.mem_univ _, ?_⟩
          rw [if_neg (fun h => h.2.ne' hj0)]
          exact mul_pos ((hW i0 j0).lt_of_ne (Ne.symm hw0)) ((hν i0).lt_of_ne (Ne.symm hi0))
      _ = ν i0 := by rw [← Finset.sum_mul, hrow, one_mul]

omit hrow in
include hW in
lemma Φ_zero (h0 : Φ ν μ W 1 = 0) (α : ℝ) : Φ ν μ W α = 0 := by
  rw [Φ_one] at h0
  have hnn : ∀ i j, 0 ≤ (if 0 < ν i ∧ 0 < μ j then W i j * ν i else 0) := by
    intro i j; split_ifs
    · exact mul_nonneg (hW i j) (hν i)
    · exact le_rfl
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg fun j _ => hnn i j)).1 h0
  unfold Φ
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnn i j)).1 (h1 i (Finset.mem_univ _)) j
    (Finset.mem_univ _)
  split_ifs at h2 ⊢ with h
  · rcases mul_eq_zero.1 h2 with h3 | h3
    · rw [h3, zero_mul]
    · exact absurd h3 h.1.ne'
  · rfl

end scalar

end X5OL
end X5mod_OL_Main

section X5mod_AM_Conv
open Matrix Filter Set
open scoped Topology

namespace X5OL

variable {I : Type*} [Fintype I] [DecidableEq I]
set_option linter.unusedSectionVars false

section conv
variable (ν μ : I → ℝ) (W : I → I → ℝ) (hW : ∀ i j, 0 ≤ W i j)
include hW

lemma Φ_nonneg_term (t : ℝ) (i j : I) :
    0 ≤ (if 0 < ν i ∧ 0 < μ j then W i j * Real.exp (t * Real.log (ν i) + (1 - t) * Real.log (μ j)) else 0) := by
  split_ifs
  · exact mul_nonneg (hW i j) (Real.exp_pos _).le
  · exact le_rfl

lemma Φ_pos (h1 : 0 < Φ ν μ W 1) (t : ℝ) : 0 < Φ ν μ W t := by
  unfold Φ at h1 ⊢
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1.ne'
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hi
  have hc : 0 < ν i ∧ 0 < μ j := by by_contra h; exact hj (if_neg h)
  have hw : W i j ≠ 0 := by intro h; apply hj; rw [if_pos hc, h, zero_mul]
  have hterm : 0 < (if 0 < ν i ∧ 0 < μ j then
      W i j * Real.exp (t * Real.log (ν i) + (1 - t) * Real.log (μ j)) else 0) := by
    rw [if_pos hc]; exact mul_pos ((hW i j).lt_of_ne (Ne.symm hw)) (Real.exp_pos _)
  refine lt_of_lt_of_le hterm ?_
  refine le_trans ?_ (Finset.single_le_sum (fun i _ => Finset.sum_nonneg fun j _ =>
    Φ_nonneg_term ν μ W hW t i j) (Finset.mem_univ i))
  exact Finset.single_le_sum (f := fun j => if 0 < ν i ∧ 0 < μ j then
      W i j * Real.exp (t * Real.log (ν i) + (1 - t) * Real.log (μ j)) else 0)
    (fun j _ => Φ_nonneg_term ν μ W hW t i j) (Finset.mem_univ j)

lemma Φ_holder (x y a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hX : 0 < Φ ν μ W x) (hY : 0 < Φ ν μ W y) :
    Φ ν μ W (a * x + b * y) ≤ Real.exp (a * Real.log (Φ ν μ W x) + b * Real.log (Φ ν μ W y)) := by
  set X := Φ ν μ W x
  set Y := Φ ν μ W y
  set E := Real.exp (a * Real.log X + b * Real.log Y)
  have key : ∀ i j, (if 0 < ν i ∧ 0 < μ j then
        W i j * Real.exp ((a * x + b * y) * Real.log (ν i) + (1 - (a * x + b * y)) * Real.log (μ j)) else 0) ≤
      E * (a * (if 0 < ν i ∧ 0 < μ j then
        W i j * Real.exp (x * Real.log (ν i) + (1 - x) * Real.log (μ j)) else 0) / X +
        b * (if 0 < ν i ∧ 0 < μ j then
        W i j * Real.exp (y * Real.log (ν i) + (1 - y) * Real.log (μ j)) else 0) / Y) := by
    intro i j
    split_ifs with hc
    · set ex := x * Real.log (ν i) + (1 - x) * Real.log (μ j)
      set ey := y * Real.log (ν i) + (1 - y) * Real.log (μ j)
      have he : (a * x + b * y) * Real.log (ν i) + (1 - (a * x + b * y)) * Real.log (μ j) =
          (a * Real.log X + b * Real.log Y) + (a * (ex - Real.log X) + b * (ey - Real.log Y)) := by
        simp only [ex, ey]
        have : b = 1 - a := by linarith
        subst this; ring
      have hcv := convexOn_exp.2 (mem_univ (ex - Real.log X)) (mem_univ (ey - Real.log Y)) ha hb hab
      simp only [smul_eq_mul] at hcv
      rw [Real.exp_sub, Real.exp_sub, Real.exp_log hX, Real.exp_log hY] at hcv
      rw [he, Real.exp_add]
      calc W i j * (E * Real.exp (a * (ex - Real.log X) + b * (ey - Real.log Y)))
          ≤ W i j * (E * (a * (Real.exp ex / X) + b * (Real.exp ey / Y))) := by
            gcongr
            exact hW i j
        _ = _ := by field_simp
    · simp
  calc Φ ν μ W (a * x + b * y) ≤ ∑ i, ∑ j, E * (a * (if 0 < ν i ∧ 0 < μ j then
        W i j * Real.exp (x * Real.log (ν i) + (1 - x) * Real.log (μ j)) else 0) / X +
        b * (if 0 < ν i ∧ 0 < μ j then
        W i j * Real.exp (y * Real.log (ν i) + (1 - y) * Real.log (μ j)) else 0) / Y) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => key i j
    _ = E * (a * X / X + b * Y / Y) := by
        simp only [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_div]
        rfl
    _ = E := by rw [mul_div_assoc, mul_div_assoc, div_self hX.ne', div_self hY.ne', mul_one, mul_one, hab,
          mul_one]

lemma L_convex (h1 : 0 < Φ ν μ W 1) : ConvexOn ℝ univ (fun t => Real.log (Φ ν μ W t)) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  have hX := Φ_pos ν μ W hW h1 x
  have hY := Φ_pos ν μ W hW h1 y
  have := Φ_holder ν μ W hW x y a b ha hb hab hX hY
  calc Real.log (Φ ν μ W (a * x + b * y))
      ≤ Real.log (Real.exp (a * Real.log (Φ ν μ W x) + b * Real.log (Φ ν μ W y))) :=
        Real.log_le_log (Φ_pos ν μ W hW h1 _) this
    _ = _ := Real.log_exp _

end conv

end X5OL
end X5mod_AM_Conv

section X5mod_OL_Thm
open Matrix Filter Set
open scoped ComplexOrder Topology

namespace X5OL
open QAlgorithms QAlgorithms.Papers.Independent.Support50.P23

attribute [local instance] Classical.propDecidable

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

lemma N_psd (sigma : Matrix B B ℂ) (hs : sigma.PosSemidef) :
    (identityTensorReference (A := A) sigma).PosSemidef := by
  unfold identityTensorReference Matrix.kronecker
  exact Matrix.PosSemidef.kronecker Matrix.PosSemidef.one hs

/-- real limit in the supported case -/
lemma real_limit {I : Type*} [Fintype I] [DecidableEq I] (ν μ : I → ℝ) (W : I → I → ℝ) (h1 : Φ ν μ W 1 = 1) :
    Tendsto (fun t => 1 / (1 - t) * Real.logb 2 (Φ ν μ W t)) (𝓝[{t : ℝ | 0 < t ∧ t ≠ 1}] 1)
      (𝓝 (-Φ' ν μ W / Real.log 2)) := by
  set ψ := fun t => Real.log (Φ ν μ W t) / Real.log 2
  have hψ : HasDerivAt ψ (Φ' ν μ W / Φ ν μ W 1 / Real.log 2) 1 :=
    ((Φ_deriv ν μ W).log (by rw [h1]; norm_num)).div_const _
  rw [h1, div_one] at hψ
  have hs := (hasDerivAt_iff_tendsto_slope.1 hψ).neg
  have hmono : 𝓝[{t : ℝ | 0 < t ∧ t ≠ 1}] (1 : ℝ) ≤ 𝓝[{(1 : ℝ)}ᶜ] 1 :=
    nhdsWithin_mono _ fun t ht => ht.2
  rw [neg_div]
  refine (hs.mono_left hmono).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht1 : t - 1 ≠ 0 := sub_ne_zero.2 ht.2
  have hψ1 : ψ 1 = 0 := by simp [ψ, h1]
  rw [slope_def_field, hψ1, sub_zero]
  simp only [ψ, Real.logb]
  field_simp
  have : (1 - t) = -(t - 1) := by ring
  rw [this]; field_simp

lemma real_atBot {I : Type*} [Fintype I] [DecidableEq I] (ν μ : I → ℝ) (W : I → I → ℝ)
    (h0 : 0 < Φ ν μ W 1) (h1 : Φ ν μ W 1 < 1) :
    Tendsto (fun t => 1 / (1 - t) * Real.logb 2 (Φ ν μ W t)) (𝓝[Ioo 0 1] 1) atBot := by
  have hC : Real.logb 2 (Φ ν μ W 1) < 0 := Real.logb_neg (by norm_num) h0 h1
  have hg : Tendsto (fun t => Real.logb 2 (Φ ν μ W t)) (𝓝[Ioo 0 1] 1) (𝓝 (Real.logb 2 (Φ ν μ W 1))) := by
    have : ContinuousAt (fun t => Real.log (Φ ν μ W t) / Real.log 2) 1 :=
      ((Φ_cont ν μ W).continuousAt.log h0.ne').div_const _
    exact this.tendsto.mono_left nhdsWithin_le_nhds
  have hsub : Tendsto (fun t : ℝ => 1 - t) (𝓝[Ioo 0 1] 1) (𝓝[Ioi 0] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have : Tendsto (fun t : ℝ => 1 - t) (𝓝 1) (𝓝 (1 - 1)) := (continuous_const.sub continuous_id).tendsto 1
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact sub_pos.2 ht.2
  have hf : Tendsto (fun t : ℝ => 1 / (1 - t)) (𝓝[Ioo 0 1] 1) atTop := by
    simp only [one_div]
    exact tendsto_inv_nhdsGT_zero.comp hsub
  exact hf.atTop_mul_neg hC hg

theorem main [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    Tendsto (finiteAlpha rho sigma)
      (nhdsWithin 1 {t : ℝ | 0 < t ∧ t ≠ 1}) (nhds (fixedVonNeumann rho sigma)) ∧
      alphaEntropy rho sigma 1 = fixedVonNeumann rho sigma := by
  refine ⟨?_, by simp [alphaEntropy, finiteAlpha]⟩
  set N := identityTensorReference (A := A) sigma with hNdef
  have hNpsd : N.PosSemidef := N_psd sigma hsigma.1
  have hR := hrho.1.isHermitian
  have hN := hNpsd.isHermitian
  set ν := hR.eigenvalues
  set μ := hN.eigenvalues
  set W := w hR hN
  have hν : ∀ i, 0 ≤ ν i := hrho.1.eigenvalues_nonneg
  have hμ : ∀ j, 0 ≤ μ j := hNpsd.eigenvalues_nonneg
  have hW : ∀ i j, 0 ≤ W i j := w_nonneg hR hN
  have hrow : ∀ i, ∑ j, W i j = 1 := w_row hR hN
  -- traces as sums
  have hcfc1 : cfc (fun _ : ℝ => (1 : ℝ)) N = 1 := cfc_const_one ℝ N hN.isSelfAdjoint
  have hsingle : ∀ f : ℝ → ℝ, (cfc f rho).trace.re = ∑ i, f (ν i) := by
    intro f
    have := tr_cfc_cfc hR hN f (fun _ => 1)
    rw [hcfc1, Matrix.mul_one] at this
    rw [this, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.re_sum]
    simp only [Complex.ofReal_re, mul_one]
    rw [← Finset.mul_sum, hrow, mul_one]
  have htr : ∑ i, ν i = 1 := by
    have := hsingle (fun x => x)
    rw [cfc_id' ℝ rho hR.isSelfAdjoint, hrho.2] at this
    simpa using this.symm
  have hF : ∀ t : ℝ, 0 < t →
      (cfc (fun x : ℝ => x ^ t) rho * cfc (fun x : ℝ => if x = 0 then 0 else x ^ (1 - t)) N).trace.re =
        Φ ν μ W t := fun t ht => tr_alpha hR hN hν hμ t ht
  have hFA : ∀ t : ℝ, 0 < t → t ≠ 1 → finiteAlpha rho sigma t =
      if 1 < t ∧ ¬ supportedBy rho N then ⊥
      else (((1 / (1 - t) : ℝ)) : EReal) * log2Extended (Φ ν μ W t) := by
    intro t ht ht1
    unfold finiteAlpha
    rw [if_neg ht1, hF t ht]
  by_cases hS : supportedBy rho N
  · -- supported case
    have hs : ∀ i j, ν i ≠ 0 → μ j = 0 → W i j = 0 := by
      intro i j hi hj
      simp only [W, w, supp_fwd hR hN hS i j hi hj, norm_zero]; norm_num
    have hΦ1 : Φ ν μ W 1 = 1 := by rw [Φ_one_supp ν μ W hν hμ hrow hs, htr]
    have hval : fixedVonNeumann rho sigma = ((-Φ' ν μ W / Real.log 2 : ℝ) : EReal) := by
      unfold fixedVonNeumann
      rw [if_pos hS, ← value_supp ν μ W hν hμ hrow hs]
      congr 2
      · have := tr_cfc_cfc hR hN (fun x => x) (fun x => Real.logb 2 x)
        rw [cfc_id' ℝ rho hR.isSelfAdjoint] at this
        rw [this, Complex.re_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Complex.re_sum]; simp only [Complex.ofReal_re]; rfl
      · unfold QAlgorithms.vnEntropy
        rw [hsingle]
    rw [hval]
    have hpos : ∀ᶠ t in 𝓝 (1 : ℝ), 0 < Φ ν μ W t :=
      (Φ_cont ν μ W).continuousAt.eventually (lt_mem_nhds (by rw [hΦ1]; norm_num))
    refine (EReal.tendsto_coe.2 (real_limit ν μ W hΦ1)).congr' ?_
    filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds hpos] with t ht hp
    rw [hFA t ht.1 ht.2, if_neg (fun h => h.2 hS)]
    unfold log2Extended
    rw [if_neg hp.ne', ← EReal.coe_mul]
  · -- unsupported case
    have hex : ∃ i j, ν i ≠ 0 ∧ μ j = 0 ∧ W i j ≠ 0 := by
      by_contra hne
      push Not at hne
      apply hS
      refine supp_bwd hR hN fun i j hi hj => ?_
      have := hne i j hi hj
      simp only [W, w] at this
      exact norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this)
    have hlt : Φ ν μ W 1 < 1 := htr ▸ Φ_one_lt ν μ W hν hμ hW hrow hex
    have hval : fixedVonNeumann rho sigma = ⊥ := by unfold fixedVonNeumann; rw [if_neg hS]
    rw [hval]
    have hset : {t : ℝ | 0 < t ∧ t ≠ 1} = Ioo 0 1 ∪ Ioi 1 := by
      ext t; simp only [mem_ofPred_eq, mem_union, mem_Ioo, mem_Ioi]
      constructor
      · rintro ⟨h0, h1⟩
        rcases lt_or_gt_of_ne h1 with h | h
        · exact Or.inl ⟨h0, h⟩
        · exact Or.inr h
      · rintro (⟨h0, h1⟩ | h)
        · exact ⟨h0, h1.ne⟩
        · exact ⟨by linarith, h.ne'⟩
    rw [hset, nhdsWithin_union]
    refine Tendsto.sup ?_ ?_
    · -- left
      have hΦnn : 0 ≤ Φ ν μ W 1 := by
        rw [Φ_one]
        exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
          split_ifs
          · exact mul_nonneg (hW i j) (hν i)
          · exact le_rfl
      rcases hΦnn.eq_or_lt with h0 | h0
      · refine tendsto_const_nhds.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with t ht
        rw [hFA t ht.1 ht.2.ne, if_neg (fun h => absurd h.1 (not_lt.2 ht.2.le)),
          Φ_zero ν μ W hν hμ hW h0.symm t]
        unfold log2Extended
        rw [if_pos rfl, EReal.coe_mul_bot_of_pos (by have := ht.2; rw [one_div]; exact inv_pos.2 (by linarith))]
      · rw [EReal.tendsto_nhds_bot_iff_real]
        intro x
        have hpos : ∀ᶠ t in 𝓝 (1 : ℝ), 0 < Φ ν μ W t :=
          (Φ_cont ν μ W).continuousAt.eventually (lt_mem_nhds h0)
        filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds hpos,
          (real_atBot ν μ W h0 hlt).eventually (eventually_lt_atBot x)] with t ht hp hlx
        rw [hFA t ht.1 ht.2.ne, if_neg (fun h => absurd h.1 (not_lt.2 ht.2.le))]
        unfold log2Extended
        rw [if_neg hp.ne', ← EReal.coe_mul, EReal.coe_lt_coe_iff]
        exact hlx
    · -- right
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      rw [hFA t (by have := ht; simp only [mem_Ioi] at this; linarith) (ne_of_gt ht), if_pos ⟨ht, hS⟩]

end X5OL
end X5mod_OL_Thm

section X5mod_AM_Thm
open Matrix Filter Set
open scoped ComplexOrder Topology ENNReal

namespace X5OL
open QAlgorithms QAlgorithms.Papers.Independent.Support50.P23

attribute [local instance] Classical.propDecidable

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

theorem fa_anti [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    AntitoneOn (finiteAlpha rho sigma) (Ioi 0) := by
  set N := identityTensorReference (A := A) sigma with hNdef
  have hNpsd : N.PosSemidef := N_psd sigma hsigma.1
  have hR := hrho.1.isHermitian
  have hN := hNpsd.isHermitian
  set ν := hR.eigenvalues
  set μ := hN.eigenvalues
  set W := w hR hN
  have hν : ∀ i, 0 ≤ ν i := hrho.1.eigenvalues_nonneg
  have hμ : ∀ j, 0 ≤ μ j := hNpsd.eigenvalues_nonneg
  have hW : ∀ i j, 0 ≤ W i j := w_nonneg hR hN
  have hrow : ∀ i, ∑ j, W i j = 1 := w_row hR hN
  have hcfc1 : cfc (fun _ : ℝ => (1 : ℝ)) N = 1 := cfc_const_one ℝ N hN.isSelfAdjoint
  have hsingle : ∀ f : ℝ → ℝ, (cfc f rho).trace.re = ∑ i, f (ν i) := by
    intro f
    have := tr_cfc_cfc hR hN f (fun _ => 1)
    rw [hcfc1, Matrix.mul_one] at this
    rw [this, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.re_sum]
    simp only [Complex.ofReal_re, mul_one]
    rw [← Finset.mul_sum, hrow, mul_one]
  have htr : ∑ i, ν i = 1 := by
    have := hsingle (fun x => x)
    rw [cfc_id' ℝ rho hR.isSelfAdjoint, hrho.2] at this
    simpa using this.symm
  have hF : ∀ t : ℝ, 0 < t →
      (cfc (fun x : ℝ => x ^ t) rho * cfc (fun x : ℝ => if x = 0 then 0 else x ^ (1 - t)) N).trace.re =
        Φ ν μ W t := fun t ht => tr_alpha hR hN hν hμ t ht
  have hFA : ∀ t : ℝ, 0 < t → t ≠ 1 → finiteAlpha rho sigma t =
      if 1 < t ∧ ¬ supportedBy rho N then ⊥
      else (((1 / (1 - t) : ℝ)) : EReal) * log2Extended (Φ ν μ W t) := by
    intro t ht ht1
    unfold finiteAlpha
    rw [if_neg ht1, hF t ht]
  have hF1 : finiteAlpha rho sigma 1 = fixedVonNeumann rho sigma := by
    unfold finiteAlpha; rw [if_pos rfl]
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  by_cases hS : supportedBy rho N
  · have hs : ∀ i j, ν i ≠ 0 → μ j = 0 → W i j = 0 := by
      intro i j hi hj
      simp only [W, w, supp_fwd hR hN hS i j hi hj, norm_zero]; norm_num
    have hΦ1 : Φ ν μ W 1 = 1 := by rw [Φ_one_supp ν μ W hν hμ hrow hs, htr]
    have hval : fixedVonNeumann rho sigma = ((-Φ' ν μ W / Real.log 2 : ℝ) : EReal) := by
      unfold fixedVonNeumann
      rw [if_pos hS, ← value_supp ν μ W hν hμ hrow hs]
      congr 2
      · have := tr_cfc_cfc hR hN (fun x => x) (fun x => Real.logb 2 x)
        rw [cfc_id' ℝ rho hR.isSelfAdjoint] at this
        rw [this, Complex.re_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Complex.re_sum]; simp only [Complex.ofReal_re]; rfl
      · unfold QAlgorithms.vnEntropy
        rw [hsingle]
    set L := fun t => Real.log (Φ ν μ W t) with hLdef
    have hconv := L_convex ν μ W hW (by rw [hΦ1]; norm_num)
    have hL : HasDerivAt L (Φ' ν μ W) 1 := by
      have := (Φ_deriv ν μ W).log (by rw [hΦ1]; norm_num)
      rwa [hΦ1, div_one] at this
    have hL1 : L 1 = 0 := by simp [hLdef, hΦ1]
    set h : ℝ → ℝ := fun t => if t = 1 then Φ' ν μ W else slope L 1 t with hhdef
    have hg : ∀ t, 0 < t → finiteAlpha rho sigma t = ((-(h t) / Real.log 2 : ℝ) : EReal) := by
      intro t ht
      by_cases ht1 : t = 1
      · subst ht1; rw [hF1, hval]; simp [hhdef]
      · rw [hFA t ht ht1, if_neg (fun h => h.2 hS)]
        have hp := Φ_pos ν μ W hW (by rw [hΦ1]; norm_num) t
        unfold log2Extended
        rw [if_neg hp.ne', ← EReal.coe_mul]
        congr 1
        simp only [hhdef, if_neg ht1, slope_def_field, sub_zero, hLdef, Real.logb, hΦ1, Real.log_one]
        have : t - 1 ≠ 0 := sub_ne_zero.2 ht1
        have : 1 - t ≠ 0 := fun h' => this (by linarith)
        field_simp
        ring
    have hmono : Monotone h := by
      intro s t hst
      rcases hst.lt_or_eq with hst | rfl
      · simp only [hhdef]
        by_cases hs1 : s = 1
        · subst hs1
          rw [if_pos rfl, if_neg hst.ne']
          exact hconv.le_slope_of_hasDerivAt (mem_univ _) (mem_univ _) hst hL
        · by_cases ht1 : t = 1
          · subst ht1
            rw [if_neg hs1, if_pos rfl, slope_comm]
            exact hconv.slope_le_of_hasDerivAt (mem_univ _) (mem_univ _) hst hL
          · rw [if_neg hs1, if_neg ht1]
            exact hconv.slope_mono (mem_univ _) ⟨mem_univ _, hs1⟩ ⟨mem_univ _, ht1⟩ hst.le
      · exact le_rfl
    intro s hs t ht hst
    rw [hg s hs, hg t ht, EReal.coe_le_coe_iff]
    have := hmono hst
    rw [div_le_div_iff_of_pos_right hl2]
    linarith
  · have hval : fixedVonNeumann rho sigma = ⊥ := by unfold fixedVonNeumann; rw [if_neg hS]
    have hex : ∃ i j, ν i ≠ 0 ∧ μ j = 0 ∧ W i j ≠ 0 := by
      by_contra hne
      push Not at hne
      apply hS
      refine supp_bwd hR hN fun i j hi hj => ?_
      have := hne i j hi hj
      simp only [W, w] at this
      exact norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this)
    have hlt : Φ ν μ W 1 < 1 := htr ▸ Φ_one_lt ν μ W hν hμ hW hrow hex
    have hbot : ∀ t, 1 ≤ t → finiteAlpha rho sigma t = ⊥ := by
      intro t ht
      rcases ht.lt_or_eq with ht | rfl
      · rw [hFA t (by linarith) ht.ne', if_pos ⟨ht, hS⟩]
      · rw [hF1, hval]
    have hΦnn : 0 ≤ Φ ν μ W 1 := by
      rw [Φ_one]
      exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
        split_ifs
        · exact mul_nonneg (hW i j) (hν i)
        · exact le_rfl
    intro s hs t ht hst
    by_cases ht1 : 1 ≤ t
    · rw [hbot t ht1]; exact bot_le
    push Not at ht1
    have hs1 : s < 1 := lt_of_le_of_lt hst ht1
    have hs0 : (0 : ℝ) < s := hs
    have ht0 : (0 : ℝ) < t := ht
    rw [hFA t ht0 ht1.ne, hFA s hs0 hs1.ne, if_neg (fun h => absurd h.1 (not_lt.2 ht1.le)),
      if_neg (fun h => absurd h.1 (not_lt.2 hs1.le))]
    rcases hΦnn.eq_or_lt with h0 | h0
    · rw [Φ_zero ν μ W hν hμ hW h0.symm t]
      unfold log2Extended
      rw [if_pos rfl, EReal.coe_mul_bot_of_pos (by rw [one_div]; exact inv_pos.2 (by linarith))]
      exact bot_le
    · have hpt := Φ_pos ν μ W hW h0 t
      have hps := Φ_pos ν μ W hW h0 s
      unfold log2Extended
      rw [if_neg hpt.ne', if_neg hps.ne', ← EReal.coe_mul, ← EReal.coe_mul, EReal.coe_le_coe_iff]
      have hconv := L_convex ν μ W hW h0
      have hL1 : Real.log (Φ ν μ W 1) < 0 := Real.log_neg h0 hlt
      set θ := (1 - t) / (1 - s)
      have h1s : 0 < 1 - s := by linarith
      have h1t : 0 < 1 - t := by linarith
      have hθ0 : 0 ≤ θ := div_nonneg h1t.le h1s.le
      have hθ1 : 0 ≤ 1 - θ := by
        simp only [θ]; rw [sub_nonneg, div_le_one h1s]; linarith
      have hc := hconv.2 (mem_univ s) (mem_univ 1) hθ0 hθ1 (by ring)
      simp only [smul_eq_mul, mul_one] at hc
      have ht' : θ * s + (1 - θ) = t := by simp only [θ]; field_simp; ring
      rw [ht'] at hc
      have hc2 : Real.log (Φ ν μ W t) ≤ θ * Real.log (Φ ν μ W s) := by
        have := mul_nonpos_of_nonneg_of_nonpos hθ1 hL1.le
        linarith
      unfold Real.logb
      have hθs : θ * (1 - s) = 1 - t := by simp only [θ]; field_simp
      have k : Real.log (Φ ν μ W t) * (1 - s) ≤ Real.log (Φ ν μ W s) * (1 - t) := by
        rw [← hθs]
        have := mul_le_mul_of_nonneg_right hc2 h1s.le
        linarith
      have e1 : ∀ (x y : ℝ), 1 / x * (y / Real.log 2) = (y / x) / Real.log 2 := fun x y => by ring
      rw [e1, e1]
      refine div_le_div_of_nonneg_right ?_ hl2.le
      rw [div_le_div_iff₀ h1t h1s]
      linarith

end X5OL

namespace X5OL
open QAlgorithms QAlgorithms.Papers.Independent.Support50.P23

attribute [local instance] Classical.propDecidable

theorem am_main {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    Antitone (alphaEntropy rho sigma) := by
  have hg := fa_anti rho sigma hrho hsigma
  have hsup : ∀ t : ℝ, 0 < t → finiteAlpha rho sigma t ≤ alphaEntropy rho sigma 0 := by
    intro t ht
    unfold alphaEntropy; rw [if_pos rfl]
    exact le_sSup ⟨t, ht, rfl⟩
  have hinf : ∀ t : ℝ, 0 < t → alphaEntropy rho sigma ⊤ ≤ finiteAlpha rho sigma t := by
    intro t ht
    unfold alphaEntropy; rw [if_neg ENNReal.top_ne_zero, if_pos rfl]
    exact sInf_le ⟨t, ht, rfl⟩
  have hfin : ∀ a : ℝ≥0∞, a ≠ 0 → a ≠ ⊤ →
      alphaEntropy rho sigma a = finiteAlpha rho sigma a.toReal ∧ 0 < a.toReal := by
    intro a h0 hT
    refine ⟨?_, ENNReal.toReal_pos h0 hT⟩
    unfold alphaEntropy; rw [if_neg h0, if_neg hT]
  intro a b hab
  by_cases ha0 : a = 0
  · subst ha0
    by_cases hb0 : b = 0
    · subst hb0; exact le_rfl
    by_cases hbT : b = ⊤
    · subst hbT; exact (hinf 1 one_pos).trans (hsup 1 one_pos)
    obtain ⟨e, hp⟩ := hfin b hb0 hbT
    rw [e]; exact hsup _ hp
  by_cases haT : a = ⊤
  · subst haT; rw [top_le_iff.1 hab]
  obtain ⟨ea, hpa⟩ := hfin a ha0 haT
  have hb0 : b ≠ 0 := fun h => ha0 (le_antisymm (h ▸ hab) bot_le)
  by_cases hbT : b = ⊤
  · subst hbT; rw [ea]; exact hinf _ hpa
  obtain ⟨eb, hpb⟩ := hfin b hb0 hbT
  rw [ea, eb]
  exact hg hpa hpb (ENNReal.toReal_mono hbT hab)

end X5OL
end X5mod_AM_Thm

section X5mod_IC_Thm
open Matrix Filter Set
open scoped ComplexOrder ComplexConjugate Topology ENNReal

namespace X5IC
open QAlgorithms QAlgorithms.Papers.Independent.Support50.P23
open QAlgorithms.Papers.Independent.Gap20.P03 (fixedMin)
set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

lemma op_eq {I : Type*} [Fintype I] [DecidableEq I] (s : NonnegativeSpectralDecomposition I) :
    s.operator = D s.basis s.values := rfl

lemma tr_formula {I : Type*} [Fintype I] [DecidableEq I] (s t : NonnegativeSpectralDecomposition I)
    (α : ℝ) (hα : 0 < α) :
    (cfc (fun x : ℝ => x ^ α) s.operator *
      cfc (fun x : ℝ => if x = 0 then 0 else x ^ (1 - α)) t.operator).trace.re =
      T s.values t.values (fun i j => ‖inner ℂ (s.basis i) (t.basis j)‖ ^ 2) α := by
  rw [op_eq, op_eq, cfc_D _ _ _ (by simp [Real.zero_rpow hα.ne']), cfc_D _ _ _ (by simp), tr_D_D,
    Complex.re_sum]
  unfold T
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.ofReal_re]

lemma spec_set {I : Type*} [Fintype I] (s t : NonnegativeSpectralDecomposition I) (ξ : ℝ) :
    {r : ℝ | ∃ i j, inner ℂ (s.basis i) (t.basis j) ≠ 0 ∧ r = s.values i / (t.values j + ξ)} =
      (fun p : I × I => s.values p.1 / (t.values p.2 + ξ)) ''
        ↑(Finset.univ.filter (fun p : I × I => inner ℂ (s.basis p.1) (t.basis p.2) ≠ 0)) := by
  ext r
  simp only [mem_ofPred_eq, Finset.coe_filter, Finset.mem_univ, true_and, mem_image, Prod.exists]
  constructor
  · rintro ⟨i, j, h, rfl⟩; exact ⟨i, j, h, rfl⟩
  · rintro ⟨i, j, h, rfl⟩; exact ⟨i, j, h, rfl⟩


lemma spec_bdd {I : Type*} [Fintype I] (s t : NonnegativeSpectralDecomposition I) (ξ : ℝ) :
    BddAbove {r : ℝ | ∃ i j, inner ℂ (s.basis i) (t.basis j) ≠ 0 ∧ r = s.values i / (t.values j + ξ)} := by
  rw [spec_set]; exact (Set.Finite.image _ (Finset.finite_toSet _)).bddAbove

lemma unsupp_tendsto {I : Type*} [Fintype I] (s t : NonnegativeSpectralDecomposition I) (i0 j0 : I)
    (hij : inner ℂ (s.basis i0) (t.basis j0) ≠ 0) (hj : t.values j0 = 0) (hi : s.values i0 ≠ 0) :
    Tendsto (spectralLog s t) (𝓝[>] 0) (𝓝 ⊥) := by
  rw [EReal.tendsto_nhds_bot_iff_real]
  intro x
  have hν : 0 < s.values i0 := lt_of_le_of_ne (s.nonnegative i0) (Ne.symm hi)
  have h2 : (0 : ℝ) < 2 ^ (-x) := by positivity
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < s.values i0 / 2 ^ (-x) by positivity)] with ξ hξ
  have hmem : s.values i0 / (t.values j0 + ξ) ∈
      {r : ℝ | ∃ i j, inner ℂ (s.basis i) (t.basis j) ≠ 0 ∧ r = s.values i / (t.values j + ξ)} :=
    ⟨i0, j0, hij, rfl⟩
  have hle := le_csSup (spec_bdd s t ξ) hmem
  rw [hj, zero_add] at hle
  have hgt : 2 ^ (-x) < s.values i0 / ξ := by
    rw [lt_div_iff₀ hξ.1]
    have := hξ.2
    rw [lt_div_iff₀ h2] at this
    linarith
  set S := sSup {r : ℝ | ∃ i j, inner ℂ (s.basis i) (t.basis j) ≠ 0 ∧ r = s.values i / (t.values j + ξ)}
  have hS : 2 ^ (-x) < S := lt_of_lt_of_le hgt hle
  have hSpos : 0 < S := lt_trans h2 hS
  unfold spectralLog log2Extended
  rw [if_neg hSpos.ne', ← EReal.coe_neg, EReal.coe_lt_coe_iff]
  have := (Real.lt_logb_iff_rpow_lt (by norm_num : (1 : ℝ) < 2) hSpos).2 hS
  linarith

lemma sup_lim {ι : Type*} (P : Finset ι) (hP : P.Nonempty) (a b : ι → ℝ)
    (h : ∀ p ∈ P, b p = 0 → a p = 0) :
    Tendsto (fun ξ : ℝ => P.sup' hP (fun p => a p / (b p + ξ))) (𝓝[>] 0)
      (𝓝 (P.sup' hP (fun p => a p / (b p + 0)))) := by
  refine Filter.Tendsto.finset_sup'_nhds_apply hP (f := fun p ξ => a p / (b p + ξ)) fun p hp => ?_
  by_cases hμz : b p = 0
  · simp only [h p hp hμz, zero_div]
    exact tendsto_const_nhds
  · exact ((continuousAt_const.div (continuousAt_const.add continuousAt_id)
      (by simpa using hμz)).tendsto).mono_left nhdsWithin_le_nhds

set_option maxHeartbeats 1000000 in
theorem main [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (s t : NonnegativeSpectralDecomposition (A × B)) (hs : s.operator = rho)
    (ht : t.operator = identityTensorReference (A := A) sigma) :
    Tendsto (spectralLog s t) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (alphaEntropy rho sigma ⊤)) ∧
      alphaEntropy rho sigma ⊤ ≤ fixedMin rho sigma := by
  set ν := s.values with hνdef
  set μ := t.values with hμdef
  set W : A × B → A × B → ℝ := fun i j => ‖inner ℂ (s.basis i) (t.basis j)‖ ^ 2 with hWdef
  have hρD : rho = D s.basis ν := hs.symm.trans (op_eq s)
  have hND : identityTensorReference (A := A) sigma = D t.basis μ := ht.symm.trans (op_eq t)
  have hsum : ∑ i, ν i = 1 := by
    have h := hrho.2
    rw [hρD, trace_D] at h
    exact_mod_cast h
  have hsupp_iff : supportedBy rho (identityTensorReference (A := A) sigma) ↔
      ∀ i j, inner ℂ (s.basis i) (t.basis j) ≠ 0 → μ j = 0 → ν i = 0 := by
    unfold supportedBy
    rw [hρD, hND]
    exact ⟨fun h => supp_fwd _ _ _ _ h, fun h => supp_bwd _ _ _ _ h⟩
  have hH : alphaEntropy rho sigma ⊤ = sInf {h : EReal | ∃ t : ℝ, 0 < t ∧ h = finiteAlpha rho sigma t} := by
    simp [alphaEntropy]
  by_cases hsp : supportedBy rho (identityTensorReference (A := A) sigma)
  swap
  · obtain ⟨i0, j0, hij, hj, hi⟩ : ∃ i j, inner ℂ (s.basis i) (t.basis j) ≠ 0 ∧ μ j = 0 ∧ ν i ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hsp (hsupp_iff.2 hc)
    have hbot : alphaEntropy rho sigma ⊤ = ⊥ := by
      rw [hH]
      refine le_bot_iff.1 (sInf_le ⟨2, two_pos, ?_⟩)
      simp [finiteAlpha, hsp]
    rw [hbot]
    exact ⟨unsupp_tendsto s t i0 j0 hij hj hi, bot_le⟩
  have hs' := hsupp_iff.1 hsp
  have hν0 : ∀ i, 0 ≤ ν i := s.nonnegative
  have hμ0 : ∀ j, 0 ≤ μ j := t.nonnegative
  have hW0 : ∀ i j, 0 ≤ W i j := fun i j => by positivity
  have hrow : ∀ i, ∑ j, W i j = 1 := fun i => row_one s.basis t.basis i
  obtain ⟨i1, hν1⟩ : ∃ i, 0 < ν i := by
    by_contra hc
    push Not at hc
    have : ∑ i, ν i ≤ 0 := Finset.sum_nonpos fun i _ => hc i
    linarith
  obtain ⟨j1, hj1⟩ : ∃ j, inner ℂ (s.basis i1) (t.basis j) ≠ 0 := by
    by_contra hc
    push Not at hc
    have := hrow i1
    simp [hWdef, hc] at this
  set P := Finset.univ.filter (fun p : (A × B) × (A × B) => inner ℂ (s.basis p.1) (t.basis p.2) ≠ 0)
    with hPdef
  have hP : P.Nonempty := ⟨(i1, j1), by simp [hPdef, hj1]⟩
  set F : ℝ → ℝ := fun ξ => P.sup' hP (fun p => ν p.1 / (μ p.2 + ξ)) with hFdef
  have hF : ∀ ξ, sSup {r : ℝ | ∃ i j, inner ℂ (s.basis i) (t.basis j) ≠ 0 ∧
      r = s.values i / (t.values j + ξ)} = F ξ := by
    intro ξ; rw [spec_set, ← Finset.sup'_eq_csSup_image]
  set M := F 0 with hMdef
  have hμ1 : μ j1 ≠ 0 := fun h => hν1.ne' (hs' i1 j1 hj1 h)
  have hMpos : 0 < M := by
    have h1 : ν i1 / (μ j1 + 0) ≤ M :=
      Finset.le_sup' (fun p : (A × B) × (A × B) => ν p.1 / (μ p.2 + 0)) (show (i1, j1) ∈ P by
        simp [hPdef, hj1])
    have h2 : 0 < ν i1 / (μ j1 + 0) := by
      rw [add_zero]; exact div_pos hν1 (lt_of_le_of_ne (hμ0 j1) (Ne.symm hμ1))
    linarith
  have hbd : ∀ i j, inner ℂ (s.basis i) (t.basis j) ≠ 0 → ν i ≤ M * μ j := by
    intro i j h
    by_cases hμz : μ j = 0
    · rw [hs' i j h hμz, hμz, mul_zero]
    have h1 : ν i / (μ j + 0) ≤ M :=
      Finset.le_sup' (fun p : (A × B) × (A × B) => ν p.1 / (μ p.2 + 0)) (show (i, j) ∈ P by
        simp [hPdef, h])
    rw [add_zero, div_le_iff₀ (lt_of_le_of_ne (hμ0 j) (Ne.symm hμz))] at h1
    exact h1
  have hbdW : ∀ i j, W i j ≠ 0 → μ j ≠ 0 → ν i ≤ M * μ j := by
    intro i j hW _
    refine hbd i j fun h => hW ?_
    simp [hWdef, h]
  obtain ⟨q, hq, hqe⟩ := Finset.exists_mem_eq_sup' hP (fun p : (A × B) × (A × B) => ν p.1 / (μ p.2 + 0))
  have hqe' : M = ν q.1 / (μ q.2 + 0) := hqe
  have hμq : 0 < μ q.2 := by
    rcases (hμ0 q.2).lt_or_eq with h | h
    · exact h
    · rw [← h, add_zero, div_zero] at hqe'; linarith
  have heq : ν q.1 = M * μ q.2 := by
    rw [hqe', add_zero, div_mul_cancel₀ _ hμq.ne']
  have hWq : 0 < W q.1 q.2 := by
    have : inner ℂ (s.basis q.1) (t.basis q.2) ≠ 0 := by simpa [hPdef] using hq
    simp only [hWdef]; positivity
  set c := μ q.2 * W q.1 q.2 with hcdef
  have hcpos : 0 < c := mul_pos hμq hWq
  have hfa : ∀ α, 1 < α → finiteAlpha rho sigma α =
      ((Real.logb 2 (T ν μ W α) / (1 - α) : ℝ) : EReal) ∧ 0 < T ν μ W α := by
    intro α hα
    have hTpos : 0 < T ν μ W α :=
      lt_of_lt_of_le (mul_pos (Real.rpow_pos_of_pos hMpos _) hcpos)
        (T_lower ν μ W M α hMpos hν0 hμ0 hW0 q.1 q.2 hμq heq)
    refine ⟨?_, hTpos⟩
    have htr := tr_formula s t α (by linarith)
    rw [hs, ht] at htr
    rw [finiteAlpha, if_neg (by linarith), if_neg (fun h => h.2 hsp), htr, log2Extended,
      if_neg hTpos.ne', ← EReal.coe_mul, one_div_mul_eq_div]
  have hL : ∀ α, 1 < α → ((-Real.logb 2 M : ℝ) : EReal) ≤ finiteAlpha rho sigma α := by
    intro α hα
    rw [(hfa α hα).1, EReal.coe_le_coe_iff, le_div_iff_of_neg (by linarith)]
    have h1 : Real.logb 2 (T ν μ W α) ≤ Real.logb 2 (M ^ (α - 1)) :=
      Real.logb_le_logb_of_le (by norm_num) (hfa α hα).2
        (T_upper ν μ W M α hα hMpos hν0 hμ0 hW0 hrow hsum hbdW)
    rw [Real.logb_rpow_eq_mul_logb_of_pos hMpos] at h1
    linarith
  have hU : ∀ α, 1 < α → finiteAlpha rho sigma α ≤
      (((Real.logb 2 c + α * Real.logb 2 M) / (1 - α) : ℝ) : EReal) := by
    intro α hα
    rw [(hfa α hα).1, EReal.coe_le_coe_iff]
    refine div_le_div_of_nonpos_of_le (by linarith) ?_
    have h1 : Real.logb 2 (M ^ α * c) ≤ Real.logb 2 (T ν μ W α) :=
      Real.logb_le_logb_of_le (by norm_num) (mul_pos (Real.rpow_pos_of_pos hMpos _) hcpos)
        (T_lower ν μ W M α hMpos hν0 hμ0 hW0 q.1 q.2 hμq heq)
    rw [Real.logb_mul (Real.rpow_pos_of_pos hMpos _).ne' hcpos.ne',
      Real.logb_rpow_eq_mul_logb_of_pos hMpos] at h1
    linarith
  have hHval : alphaEntropy rho sigma ⊤ = ((-Real.logb 2 M : ℝ) : EReal) := by
    rw [hH]
    apply le_antisymm
    · refine ge_of_tendsto ((continuous_coe_real_ereal.tendsto _).comp (q_tendsto (Real.logb 2 c)
        (Real.logb 2 M))) ?_
      filter_upwards [eventually_gt_atTop 1] with α hα
      exact (sInf_le (show finiteAlpha rho sigma α ∈
        {h : EReal | ∃ t : ℝ, 0 < t ∧ h = finiteAlpha rho sigma t} from ⟨α, by linarith, rfl⟩)).trans (hU α hα)
    · refine le_sInf ?_
      rintro _ ⟨τ, hτ, rfl⟩
      by_cases hτ1 : 1 < τ
      · exact hL τ hτ1
      · exact (hL 2 (by norm_num)).trans
          (X5OL.fa_anti rho sigma hrho hsigma (show τ ∈ Ioi (0 : ℝ) from hτ)
            (show (2 : ℝ) ∈ Ioi (0 : ℝ) by norm_num) (by linarith))
  refine ⟨?_, ?_⟩
  · rw [hHval]
    have hlim : Tendsto F (𝓝[>] 0) (𝓝 M) :=
      sup_lim P hP (fun p => ν p.1) (fun p => μ p.2) fun p hp hμz =>
        hs' p.1 p.2 (by simpa [hPdef] using hp) hμz
    have hev : ∀ᶠ ξ in 𝓝[>] (0 : ℝ), spectralLog s t ξ = ((-Real.logb 2 (F ξ) : ℝ) : EReal) := by
      filter_upwards [hlim.eventually (lt_mem_nhds hMpos)] with ξ hξ
      unfold spectralLog log2Extended
      rw [hF ξ, if_neg hξ.ne', EReal.coe_neg]
    refine Tendsto.congr' (EventuallyEq.symm hev) ?_
    exact (continuous_coe_real_ereal.tendsto _).comp
      (((Real.continuousAt_logb hMpos.ne').tendsto.comp hlim).neg)
  · rw [hHval]
    unfold fixedMin
    refine le_sSup ⟨-Real.logb 2 M, rfl, ?_⟩
    have h2 : Real.rpow 2 (-(-Real.logb 2 M)) = M := by
      rw [neg_neg]; exact Real.rpow_logb (by norm_num) (by norm_num) hMpos
    rw [h2]
    have := psd s.basis t.basis ν μ hν0 hμ0 M hMpos.le hbd
    rw [← op_eq, ← op_eq, ht, hs] at this
    exact this

end X5IC
end X5mod_IC_Thm

noncomputable section

open Filter

open scoped ENNReal ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P23

open QAlgorithms.Papers.Independent.Gap20.P03 (fixedMin)

theorem solution {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (s t : NonnegativeSpectralDecomposition (A × B)) (hs : s.operator = rho)
    (ht : t.operator = identityTensorReference (A := A) sigma) :
    Tendsto (spectralLog s t) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (alphaEntropy rho sigma ⊤)) ∧
      alphaEntropy rho sigma ⊤ ≤ fixedMin rho sigma :=
  X5IC.main rho sigma hrho hsigma s t hs ht

end
