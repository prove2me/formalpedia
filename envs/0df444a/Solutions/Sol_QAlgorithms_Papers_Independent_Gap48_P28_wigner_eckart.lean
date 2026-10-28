-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P28.wigner_eckart
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T10:38:19.167974+00:00
-- url     : https://prove2.me/submissions/ab815342-a67e-4b89-b6f2-e8c3e3ef149a

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P28
noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P28

open scoped Matrix Kronecker ComplexConjugate

lemma S170D_tPA {d n : ℕ} (σ : Equiv.Perm (Fin n)) (A : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ)
    (x y : Fin n → Fin d) :
    (QAlgorithms.Schur.tensorPermutation d n σ * A) x y = A (x ∘ σ) y := by
  simp only [Matrix.mul_apply, QAlgorithms.Schur.tensorPermutation, Matrix.of_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single (x ∘ σ)]
  · rw [if_pos (by ext k; simp)]
  · intro b _ hb; rw [if_neg]; intro h; apply hb; rw [h]; ext k; simp
  · simp

lemma S170D_AtP {d n : ℕ} (σ : Equiv.Perm (Fin n)) (A : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ)
    (x y : Fin n → Fin d) :
    (A * QAlgorithms.Schur.tensorPermutation d n σ) x y = A x (y ∘ σ.symm) := by
  simp only [Matrix.mul_apply, QAlgorithms.Schur.tensorPermutation, Matrix.of_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (y ∘ σ.symm)]
  · rw [if_pos rfl]
  · intro b _ hb; rw [if_neg hb]
  · simp

lemma S170D_pk_tP {d n : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) (σ : Equiv.Perm (Fin n)) :
    piKron n U * QAlgorithms.Schur.tensorPermutation d n σ =
      QAlgorithms.Schur.tensorPermutation d n σ * piKron n U := by
  ext x y
  rw [S170D_AtP, S170D_tPA]
  simp only [piKron, Matrix.of_apply, Function.comp_apply]
  rw [← Equiv.prod_comp σ]
  simp

lemma S170D_pk_H {d n : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) : (piKron n U)ᴴ = piKron n Uᴴ := by
  ext x y
  simp [piKron, Matrix.conjTranspose_apply]

lemma S170D_pk_mul {d n : ℕ} (U V : Matrix (Fin d) (Fin d) ℂ) :
    piKron n U * piKron n V = piKron n (U * V) := by
  ext x y
  simp only [Matrix.mul_apply, piKron, Matrix.of_apply, ← Finset.prod_mul_distrib]
  rw [Fintype.prod_sum (fun i c => U (x i) c * V c (y i))]

lemma S170D_pk_one {d n : ℕ} : piKron n (1 : Matrix (Fin d) (Fin d) ℂ) = 1 := by
  ext x y
  simp only [piKron, Matrix.of_apply, Matrix.one_apply]
  by_cases hxy : x = y
  · subst hxy; simp
  · rw [if_neg hxy]
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
      by_contra H; exact hxy (funext fun i => not_not.mp (fun hi => H ⟨i, hi⟩))
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

lemma S170D_pk_Y {d n : ℕ} (lambda : QAlgorithms.Schur.Partition d n) (U : Matrix (Fin d) (Fin d) ℂ) :
    piKron n U * QAlgorithms.Schur.tensorYoungOperator lambda =
      QAlgorithms.Schur.tensorYoungOperator lambda * piKron n U := by
  unfold QAlgorithms.Schur.tensorYoungOperator
  simp only [Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul, S170D_pk_tP]

lemma S170D_mem {d n : ℕ} (lambda : QAlgorithms.Schur.Partition d n) (U : Matrix (Fin d) (Fin d) ℂ)
    (v : EuclideanSpace ℂ (Fin n → Fin d)) (hv : v ∈ QAlgorithms.Schur.schurModule lambda) :
    Matrix.toEuclideanLin (piKron n U) v ∈ QAlgorithms.Schur.schurModule lambda := by
  obtain ⟨w, rfl⟩ := hv
  refine ⟨Matrix.toEuclideanLin (piKron n U) w, ?_⟩
  simp only [Matrix.toEuclideanLin_apply, WithLp.ofLp_toLp, Matrix.mulVec_mulVec, S170D_pk_Y]

lemma S170D_inner {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (hA : Aᴴ * A = 1)
    (v w : EuclideanSpace ℂ ι) :
    inner ℂ (Matrix.toEuclideanLin A v) (Matrix.toEuclideanLin A w) = inner ℂ v w := by
  rw [← LinearMap.adjoint_inner_right, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  congr 1
  simp only [Matrix.toEuclideanLin_apply, WithLp.ofLp_toLp, Matrix.mulVec_mulVec, hA, Matrix.one_mulVec]

lemma S170D_rep {d n : ℕ} (lambda : QAlgorithms.Schur.Partition d n) (U : Matrix (Fin d) (Fin d) ℂ)
    (v : QAlgorithms.Schur.schurModule lambda) :
    ((QAlgorithms.Schur.polynomialRepresentation lambda U v : QAlgorithms.Schur.schurModule lambda) :
      EuclideanSpace ℂ (Fin n → Fin d)) = Matrix.toEuclideanLin (piKron n U) v := by
  unfold QAlgorithms.Schur.polynomialRepresentation
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype, ContinuousLinearMap.coe_coe]
  rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (K := QAlgorithms.Schur.schurModule lambda)
    ⟨_, S170D_mem lambda U v v.2⟩]

lemma S170D_unitary {d n : ℕ} (lambda : QAlgorithms.Schur.Partition d n)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ (QAlgorithms.Schur.schurModule lambda))
    (u : Matrix.unitaryGroup (Fin d) ℂ) :
    (irrepMatrix lambda b u)ᴴ * irrepMatrix lambda b u = 1 := by
  have hu : (u : Matrix (Fin d) (Fin d) ℂ)ᴴ * (u : Matrix (Fin d) (Fin d) ℂ) = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.mp u.2
    rwa [Matrix.star_eq_conjTranspose] at this
  have hP : (piKron n (u : Matrix (Fin d) (Fin d) ℂ))ᴴ * piKron n (u : Matrix (Fin d) (Fin d) ℂ) = 1 := by
    rw [S170D_pk_H, S170D_pk_mul, hu, S170D_pk_one]
  refine Matrix.ext fun c c' => ?_
  rw [Matrix.one_apply]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, irrepMatrix, RCLike.star_def]
  have hc : ∀ j, (starRingEnd ℂ) (inner ℂ (b j) (QAlgorithms.Schur.polynomialRepresentation lambda
      (u : Matrix (Fin d) (Fin d) ℂ) (b c))) =
      inner ℂ (QAlgorithms.Schur.polynomialRepresentation lambda (u : Matrix (Fin d) (Fin d) ℂ) (b c)) (b j) :=
    fun j => inner_conj_symm (𝕜 := ℂ) (E := QAlgorithms.Schur.schurModule lambda) _ _
  simp only [hc]
  rw [OrthonormalBasis.sum_inner_mul_inner]
  rw [Submodule.coe_inner, S170D_rep, S170D_rep, S170D_inner _ hP, ← Submodule.coe_inner]
  exact orthonormal_iff_ite.1 b.orthonormal c c'

end QAlgorithms.Papers.Independent.Gap48.P28

open QAlgorithms.Papers.Independent.Gap48.P28
open scoped Matrix Kronecker ComplexConjugate

theorem solution
    (d nMu nNu nLambda : ℕ) (hd : 1 ≤ d)
    (mu : QAlgorithms.Schur.Partition d nMu)
    (nu : QAlgorithms.Schur.Partition d nNu)
    (lambda : QAlgorithms.Schur.Partition d nLambda)
    {M N L A : Type*}
    [Fintype M] [DecidableEq M] [Nonempty M]
    [Fintype N] [DecidableEq N] [Nonempty N]
    [Fintype L] [DecidableEq L] [Nonempty L]
    [Fintype A] [DecidableEq A]
    (bMu : OrthonormalBasis M ℂ (QAlgorithms.Schur.schurModule mu))
    (bNu : OrthonormalBasis N ℂ (QAlgorithms.Schur.schurModule nu))
    (bLambda : OrthonormalBasis L ℂ (QAlgorithms.Schur.schurModule lambda))
    (b : Module.Basis A ℂ (intertwinerSpace
      (irrepMatrix mu bMu) (irrepMatrix nu bNu) (irrepMatrix lambda bLambda)))
    (hNormalization : ∀ a c : A,
      (b a).val * ((b c).val)ᴴ = if a = c then 1 else 0)
    (t : N → Matrix L M ℂ)
    (hCovariance : ∀ (u : Matrix.unitaryGroup (Fin d) ℂ) (qNu : N),
      irrepMatrix lambda bLambda u * t qNu *
          (irrepMatrix mu bMu u)ᴴ =
        ∑ qNuNext : N, (irrepMatrix nu bNu u qNuNext qNu) • t qNuNext) :
    ∃ reduced : A → ℂ, ∀ (qMu : M) (qNu : N) (qLambda : L),
      t qNu qLambda qMu =
        ∑ a : A, reduced a * cgBlockEntry b a qLambda qMu qNu := by
  set T : Matrix L (M × N) ℂ := Matrix.of fun l p => t p.2 l p.1 with hTdef
  have hT : T ∈ intertwinerSpace (irrepMatrix mu bMu) (irrepMatrix nu bNu) (irrepMatrix lambda bLambda) := by
    intro u
    have hcov : ∀ n, irrepMatrix lambda bLambda u * t n =
        (∑ n' : N, (irrepMatrix nu bNu u n' n) • t n') * irrepMatrix mu bMu u := by
      intro n
      rw [← hCovariance u n, Matrix.mul_assoc _ (irrepMatrix mu bMu u)ᴴ, S170D_unitary, Matrix.mul_one]
    refine Matrix.ext fun l p => ?_
    obtain ⟨m, n⟩ := p
    have e1 : (irrepMatrix lambda bLambda u * T) l (m, n) = (irrepMatrix lambda bLambda u * t n) l m := by
      simp [Matrix.mul_apply, hTdef]
    rw [e1, hcov n]
    simp only [Matrix.mul_apply, Matrix.kroneckerMap_apply, hTdef, Matrix.of_apply, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul, Fintype.sum_prod_type, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m' _ => Finset.sum_congr rfl fun n' _ => ?_
    ring
  refine ⟨fun a => b.repr ⟨T, hT⟩ a, fun qMu qNu qLambda => ?_⟩
  have hs := congrArg (fun x : intertwinerSpace (irrepMatrix mu bMu) (irrepMatrix nu bNu)
    (irrepMatrix lambda bLambda) => (x : Matrix L (M × N) ℂ) qLambda (qMu, qNu)) (b.sum_repr ⟨T, hT⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] at hs
  simp only [cgBlockEntry]
  rw [hs]
  rfl
