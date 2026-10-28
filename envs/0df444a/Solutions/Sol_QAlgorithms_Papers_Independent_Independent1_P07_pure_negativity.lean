-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P07.pure_negativity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T08:26:30.108596+00:00
-- url     : https://prove2.me/submissions/987a0751-9fbe-479c-9538-e9c68cb2e641

import Definitions.Def_QAlgorithms_Defs_EntanglementNegativity
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Defs_QuditChannelFidelities
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P07_Model
set_option autoImplicit false

noncomputable section

open scoped Matrix ComplexOrder NNReal ENNReal

namespace QAlgorithms.Papers.Independent.Independent1.P07

open Entanglement

open Matrix ComplexConjugate

def PN_R {n : Type*} (a b : EuclideanSpace ℂ n) : Matrix n n ℂ :=
  Matrix.of fun i j => a i * conj (b j)

lemma PN_inner_eq {n : Type*} [Fintype n] (a b : EuclideanSpace ℂ n) :
    inner ℂ a b = ∑ i, conj (a i) * b i := by
  rw [PiLp.inner_apply]; simp [mul_comm]

lemma PN_R_mul {n : Type*} [Fintype n] (a b c d : EuclideanSpace ℂ n) :
    PN_R a b * PN_R c d = (inner ℂ b c) • PN_R a d := by
  ext i j
  simp only [PN_R, Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply, PN_inner_eq,
    smul_eq_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => by ring

lemma PN_R_conjTranspose {n : Type*} (a b : EuclideanSpace ℂ n) :
    (PN_R a b)ᴴ = PN_R b a := by
  ext i j; simp [PN_R, mul_comm]

lemma PN_R_trace {n : Type*} [Fintype n] (a b : EuclideanSpace ℂ n) :
    (PN_R a b).trace = inner ℂ b a := by
  simp [PN_R, Matrix.trace, PN_inner_eq, mul_comm]

def PN_D {n K : Type*} [Fintype K] (w : K → EuclideanSpace ℂ n) (g : K → ℝ) :
    Matrix n n ℂ := ∑ k, ((g k : ℝ) : ℂ) • PN_R (w k) (w k)

lemma PN_D_mul {n K : Type*} [Fintype n] [Fintype K] (w : K → EuclideanSpace ℂ n)
    (hw : Orthonormal ℂ w) (g h : K → ℝ) :
    PN_D w g * PN_D w h = PN_D w (g * h) := by
  classical
  rw [orthonormal_iff_ite] at hw
  simp only [PN_D, Finset.sum_mul, Finset.mul_sum, smul_mul_smul, PN_R_mul, hw, smul_smul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hb; simp [hb]
  · simp

lemma PN_D_add {n K : Type*} [Fintype K] (w : K → EuclideanSpace ℂ n) (g h : K → ℝ) :
    PN_D w (g + h) = PN_D w g + PN_D w h := by
  simp [PN_D, add_smul, Finset.sum_add_distrib]

lemma PN_D_smul {n K : Type*} [Fintype K] (w : K → EuclideanSpace ℂ n) (a : ℝ) (g : K → ℝ) :
    PN_D w (a • g) = a • PN_D w g := by
  simp [PN_D, Finset.smul_sum, smul_smul, ← Complex.coe_smul]

lemma PN_D_trace {n K : Type*} [Fintype n] [Fintype K] (w : K → EuclideanSpace ℂ n)
    (hw : Orthonormal ℂ w) (g : K → ℝ) :
    (PN_D w g).trace = ((∑ k, g k : ℝ) : ℂ) := by
  simp [PN_D, Matrix.trace_sum, PN_R_trace, hw.1]

lemma PN_D_selfAdjoint {n K : Type*} [Fintype K] (w : K → EuclideanSpace ℂ n) (g : K → ℝ) :
    IsSelfAdjoint (PN_D w g) := by
  show (PN_D w g)ᴴ = PN_D w g
  simp [PN_D, Matrix.conjTranspose_sum, PN_R_conjTranspose]

lemma PN_Q_mul {n K : Type*} [Fintype n] [DecidableEq n] [Fintype K]
    (w : K → EuclideanSpace ℂ n) (hw : Orthonormal ℂ w) (g : K → ℝ) :
    (1 - PN_D w 1) * PN_D w g = 0 := by
  rw [sub_mul, one_mul, PN_D_mul w hw, one_mul, sub_self]

lemma PN_aeval {n K : Type*} [Fintype n] [DecidableEq n] [Fintype K]
    (w : K → EuclideanSpace ℂ n) (hw : Orthonormal ℂ w) (μ : K → ℝ) (p : Polynomial ℝ) :
    Polynomial.aeval (PN_D w μ) p
      = (p.eval 0) • (1 - PN_D w 1) + PN_D w (fun k => p.eval (μ k)) := by
  induction p using Polynomial.induction_on with
  | C a =>
    simp only [Polynomial.aeval_C, Polynomial.eval_C, Algebra.algebraMap_eq_smul_one]
    have : (fun _ : K => a) = a • (1 : K → ℝ) := by ext; simp
    rw [this, PN_D_smul, smul_sub]; abel
  | add p q hp hq =>
    rw [map_add, hp, hq, Polynomial.eval_add, add_smul]
    have : (fun k => (p + q).eval (μ k)) = (fun k => p.eval (μ k)) + (fun k => q.eval (μ k)) := by
      ext; simp
    rw [this, PN_D_add]; abel
  | monomial m a h =>
    rw [pow_succ, ← mul_assoc, map_mul, h, Polynomial.aeval_X, add_mul, smul_mul_assoc,
      PN_Q_mul w hw, smul_zero, zero_add, PN_D_mul w hw]
    simp only [Polynomial.eval_mul, Polynomial.eval_X, mul_zero, zero_smul, zero_add]
    rfl

lemma PN_spectrum {n K : Type*} [Fintype n] [DecidableEq n] [Fintype K]
    (w : K → EuclideanSpace ℂ n) (hw : Orthonormal ℂ w) (μ : K → ℝ) (x : ℝ)
    (hx : x ∈ spectrum ℝ (PN_D w μ)) : x = 0 ∨ ∃ k, x = μ k := by
  set q : Polynomial ℝ := Polynomial.X * ∏ k, (Polynomial.X - Polynomial.C (μ k)) with hq
  have h0 : Polynomial.aeval (PN_D w μ) q = 0 := by
    rw [PN_aeval w hw]
    have h1 : q.eval 0 = 0 := by simp [hq]
    have h2 : (fun k => q.eval (μ k)) = 0 := by
      ext k; simp only [hq, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_prod,
        Polynomial.eval_sub, Polynomial.eval_C, Pi.zero_apply]
      rw [Finset.prod_eq_zero (Finset.mem_univ k) (by simp), mul_zero]
    rw [h1, h2]; simp [PN_D]
  have hmem := spectrum.subset_polynomial_aeval (PN_D w μ) q ⟨x, hx, rfl⟩
  rw [h0] at hmem
  have hev : q.eval x = 0 := by
    by_contra hne
    apply spectrum.notMem_iff.mpr _ hmem
    simpa using (IsUnit.mk0 _ hne).map (algebraMap ℝ (Matrix n n ℂ))
  simp only [hq, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_prod,
        Polynomial.eval_sub, Polynomial.eval_C, mul_eq_zero, Finset.prod_eq_zero_iff,
        sub_eq_zero] at hev
  rcases hev with h | ⟨k, _, hk⟩
  · exact Or.inl h
  · exact Or.inr ⟨k, hk⟩

lemma PN_cfc {n K : Type*} [Fintype n] [DecidableEq n] [Fintype K]
    (w : K → EuclideanSpace ℂ n) (hw : Orthonormal ℂ w) (μ : K → ℝ) (f : ℝ → ℝ)
    (hf : f 0 = 0) : cfc f (PN_D w μ) = PN_D w (fun k => f (μ k)) := by
  classical
  set s : Finset ℝ := insert 0 (Finset.univ.image μ)
  set p : Polynomial ℝ := Lagrange.interpolate s id f
  have hp : ∀ x ∈ s, p.eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (v := id) f (Set.injOn_id _) hx
  have hA := PN_D_selfAdjoint w μ
  rw [cfc_congr (g := fun x => p.eval x) (a := PN_D w μ)]
  · rw [cfc_polynomial p (PN_D w μ) hA, PN_aeval w hw, hp 0 (by simp [s]), hf, zero_smul,
      zero_add]
    congr 1; ext k; exact hp _ (by simp [s])
  · intro x hx
    refine (hp x ?_).symm
    rcases PN_spectrum w hw μ x hx with h | ⟨k, h⟩ <;> simp [s, h]

lemma PN_schmidt_apply {I J : Type*} {r : ℕ} (c : Fin r → ℝ)
    (u : Fin r → EuclideanSpace ℂ I) (v : Fin r → EuclideanSpace ℂ J) (p : I × J) :
    (schmidtState c u v) p = ∑ i, (c i : ℂ) * (u i p.1 * v i p.2) := by
  simp [schmidtState, tensorVec]

lemma PN_MHM {n K : Type*} [Fintype n] [Fintype K] (w : K → EuclideanSpace ℂ n)
    (hw : Orthonormal ℂ w) (σ : K → K) (hσ : Function.Injective σ) (a : K → ℝ) :
    (∑ k, ((a k : ℝ) : ℂ) • PN_R (w (σ k)) (w k))ᴴ * (∑ k, ((a k : ℝ) : ℂ) • PN_R (w (σ k)) (w k))
      = PN_D w (fun k => a k ^ 2) := by
  classical
  rw [orthonormal_iff_ite] at hw
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, PN_R_conjTranspose,
    Finset.sum_mul, Finset.mul_sum, smul_mul_smul, PN_R_mul, hw, hσ.eq_iff, smul_smul, PN_D,
    Complex.star_def, Complex.conj_ofReal]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single k (fun b _ hb => by simp [hb]) (by simp)]
  simp [sq]

def PN_cv {n : Type*} (a : EuclideanSpace ℂ n) : EuclideanSpace ℂ n :=
  WithLp.toLp 2 (fun i => conj (a i))

lemma PN_inner_tensor {I J : Type*} [Fintype I] [Fintype J] (a c : EuclideanSpace ℂ I)
    (b d : EuclideanSpace ℂ J) :
    inner ℂ (tensorVec a b) (tensorVec c d) = inner ℂ a c * inner ℂ b d := by
  simp only [PN_inner_eq, tensorVec, Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp; ring

lemma PN_inner_cv {I : Type*} [Fintype I] (a c : EuclideanSpace ℂ I) :
    inner ℂ (PN_cv a) (PN_cv c) = inner ℂ c a := by
  simp only [PN_inner_eq, PN_cv]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp; ring

lemma PN_x_orth {I J : Type*} [Fintype I] [Fintype J] {r : ℕ}
    (u : Fin r → EuclideanSpace ℂ I) (v : Fin r → EuclideanSpace ℂ J)
    (hu : Orthonormal ℂ u) (hv : Orthonormal ℂ v) :
    Orthonormal ℂ (fun p : Fin r × Fin r => tensorVec (PN_cv (u p.1)) (v p.2)) := by
  classical
  rw [orthonormal_iff_ite] at hu hv ⊢
  rintro ⟨i, l⟩ ⟨i', l'⟩
  simp only [PN_inner_tensor, PN_inner_cv, hu, hv, Prod.mk.injEq]
  by_cases h1 : i = i' <;> by_cases h2 : l = l' <;> simp [h1, h2, eq_comm]

lemma PN_PT {I J : Type*} [Fintype I] [Fintype J] {r : ℕ} (c : Fin r → ℝ)
    (u : Fin r → EuclideanSpace ℂ I) (v : Fin r → EuclideanSpace ℂ J) :
    partialTransposeFirst (pureDensity (schmidtState c u v)) =
      ∑ k : Fin r × Fin r, ((c k.1 * c k.2 : ℝ) : ℂ) •
        PN_R ((fun p : Fin r × Fin r => tensorVec (PN_cv (u p.1)) (v p.2)) (Prod.swap k))
          ((fun p : Fin r × Fin r => tensorVec (PN_cv (u p.1)) (v p.2)) k) := by
  ext p q
  simp only [partialTransposeFirst, pureDensity, Matrix.of_apply, PN_schmidt_apply,
    Matrix.sum_apply, Matrix.smul_apply, PN_R, tensorVec, PN_cv, Prod.fst_swap, Prod.snd_swap,
    map_sum, map_mul, Complex.conj_ofReal, Finset.sum_mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  simp; ring


lemma PN_tn {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] {r : ℕ}
    (c : Fin r → ℝ) (u : Fin r → EuclideanSpace ℂ I) (v : Fin r → EuclideanSpace ℂ J)
    (hc : ∀ i, 0 ≤ c i) (hu : Orthonormal ℂ u) (hv : Orthonormal ℂ v) :
    traceNorm (partialTransposeFirst (pureDensity (schmidtState c u v))) = (∑ i, c i) ^ 2 := by
  rw [traceNorm, PN_PT,
    PN_MHM _ (PN_x_orth u v hu hv) Prod.swap Prod.swap_injective,
    PN_cfc _ (PN_x_orth u v hu hv) _ _ Real.sqrt_zero, PN_D_trace _ (PN_x_orth u v hu hv),
    Complex.ofReal_re]
  rw [sq, Finset.sum_mul_sum, ← Finset.sum_product']
  refine Finset.sum_congr rfl fun k _ => ?_
  exact Real.sqrt_sq (mul_nonneg (hc _) (hc _))

def PN_qf {n : Type*} [Fintype n] (a b : EuclideanSpace ℂ n) : Matrix n n ℂ →ₗ[ℂ] ℂ where
  toFun X := ∑ p, ∑ q, conj (a p) * X p q * b q
  map_add' X Y := by
    simp only [Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' t X := by
    simp only [Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring

lemma PN_qf_apply {n : Type*} [Fintype n] (a b : EuclideanSpace ℂ n) (X : Matrix n n ℂ) :
    PN_qf a b X = ∑ p, ∑ q, conj (a p) * X p q * b q := rfl

lemma PN_qf_pd {n : Type*} [Fintype n] (a b ψ : EuclideanSpace ℂ n) :
    PN_qf a b (pureDensity ψ) = inner ℂ a ψ * inner ℂ ψ b := by
  simp only [PN_qf_apply, pureDensity, Matrix.of_apply, PN_inner_eq, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring

lemma PN_qf_kron {I J : Type*} [Fintype I] [Fintype J] (a c : EuclideanSpace ℂ I)
    (b d : EuclideanSpace ℂ J) (A : Matrix I I ℂ) (B : Matrix J J ℂ) :
    PN_qf (tensorVec a b) (tensorVec c d) (Matrix.kronecker A B) = PN_qf a c A * PN_qf b d B := by
  simp only [PN_qf_apply, tensorVec, Fintype.sum_prod_type, Finset.sum_mul_sum,
    ]
  refine Finset.sum_congr rfl fun p1 _ => Finset.sum_congr rfl fun p2 _ =>
    Finset.sum_congr rfl fun q1 _ => Finset.sum_congr rfl fun q2 _ => ?_
  simp [Matrix.kronecker, Matrix.kroneckerMap_apply]; ring

def PN_F {I J : Type*} [Fintype I] [Fintype J] {r : ℕ}
    (u : Fin r → EuclideanSpace ℂ I) (v : Fin r → EuclideanSpace ℂ J) :
    Matrix (I × J) (I × J) ℂ →ₗ[ℂ] ℂ :=
  (∑ j, ∑ k, PN_qf (tensorVec (u j) (v k)) (tensorVec (u j) (v k))) -
    ∑ j, ∑ k, PN_qf (tensorVec (u j) (v j)) (tensorVec (u k) (v k))

lemma PN_F_apply {I J : Type*} [Fintype I] [Fintype J] {r : ℕ}
    (u : Fin r → EuclideanSpace ℂ I) (v : Fin r → EuclideanSpace ℂ J) (X) :
    PN_F u v X = (∑ j, ∑ k, PN_qf (tensorVec (u j) (v k)) (tensorVec (u j) (v k)) X) -
      ∑ j, ∑ k, PN_qf (tensorVec (u j) (v j)) (tensorVec (u k) (v k)) X := by
  simp [PN_F, LinearMap.sum_apply]

lemma PN_inner_e_psi {I J : Type*} [Fintype I] [Fintype J] {r : ℕ} (c : Fin r → ℝ)
    (u : Fin r → EuclideanSpace ℂ I) (v : Fin r → EuclideanSpace ℂ J)
    (hu : Orthonormal ℂ u) (hv : Orthonormal ℂ v) (j k : Fin r) :
    inner ℂ (tensorVec (u j) (v k)) (schmidtState c u v) = if j = k then (c j : ℂ) else 0 := by
  classical
  rw [orthonormal_iff_ite] at hu hv
  rw [schmidtState, inner_sum]
  simp only [inner_smul_right, PN_inner_tensor, hu, hv]
  by_cases h : j = k
  · subst h; simp
  · simp [h]

lemma PN_F_rho {I J : Type*} [Fintype I] [Fintype J] {r : ℕ} (c : Fin r → ℝ)
    (u : Fin r → EuclideanSpace ℂ I) (v : Fin r → EuclideanSpace ℂ J)
    (hu : Orthonormal ℂ u) (hv : Orthonormal ℂ v) :
    PN_F u v (pureDensity (schmidtState c u v)) =
      (((∑ i, c i ^ 2) - (∑ i, c i) ^ 2 : ℝ) : ℂ) := by
  rw [PN_F_apply]
  simp only [PN_qf_pd]
  simp only [← inner_conj_symm (schmidtState c u v), PN_inner_e_psi c u v hu hv]
  simp [sq, Finset.sum_mul_sum]

def PN_mv {n : Type*} [Fintype n] (L : Matrix n n ℂ) (a : EuclideanSpace ℂ n) :
    EuclideanSpace ℂ n := WithLp.toLp 2 (fun m => ∑ q, L m q * a q)

lemma PN_qf_gram {n : Type*} [Fintype n] (L : Matrix n n ℂ) (a b : EuclideanSpace ℂ n) :
    PN_qf a b (Lᴴ * L) = inner ℂ (PN_mv L a) (PN_mv L b) := by
  simp only [PN_qf_apply, PN_inner_eq, PN_mv, Matrix.mul_apply, Matrix.conjTranspose_apply,
    map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_congr rfl fun p _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ => ?_
  simp; ring

lemma PN_bessel {n : Type*} [Fintype n] {r : ℕ} (L : Matrix n n ℂ) (u : Fin r → EuclideanSpace ℂ n)
    (hu : Orthonormal ℂ u) : ∑ j, ‖PN_mv L (u j)‖ ^ 2 ≤ (Lᴴ * L).trace.re := by
  set row : n → EuclideanSpace ℂ n := fun m => WithLp.toLp 2 (fun q => conj (L m q))
  have h1 : ∀ x : EuclideanSpace ℂ n, ‖PN_mv L x‖ ^ 2 = ∑ m, ‖inner ℂ (x) (row m)‖ ^ 2 := by
    intro x
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← inner_conj_symm, Complex.norm_conj, PN_inner_eq]
    simp [PN_mv, row]
  have h2 : (Lᴴ * L).trace.re = ∑ m, ‖row m‖ ^ 2 := by
    simp only [EuclideanSpace.norm_sq_eq, row, Matrix.trace, Matrix.diag, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Complex.re_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun q _ => ?_
    simp
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  rw [h2]
  simp only [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun m _ => ?_
  have := hu.sum_inner_products_le (x := row m) (s := Finset.univ)
  simpa only [← inner_conj_symm (row m), Complex.norm_conj] using this

lemma PN_tensor_norm {I J : Type*} [Fintype I] [Fintype J] (x : EuclideanSpace ℂ I)
    (y : EuclideanSpace ℂ J) : ‖tensorVec x y‖ = ‖x‖ * ‖y‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq,
    ← Real.sqrt_mul (Finset.sum_nonneg fun _ _ => by positivity)]
  congr 1
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  simp [tensorVec, mul_pow]

open scoped MatrixOrder in
lemma PN_prod_bound {I J : Type*} [Fintype I] [Fintype J] {r : ℕ}
    (u : Fin r → EuclideanSpace ℂ I) (v : Fin r → EuclideanSpace ℂ J)
    (hu : Orthonormal ℂ u) (hv : Orthonormal ℂ v) (A : Matrix I I ℂ) (B : Matrix J J ℂ)
    (hA : IsDensityMatrix A) (hB : IsDensityMatrix B) :
    0 ≤ (PN_F u v (Matrix.kronecker A B)).re ∧ (PN_F u v (Matrix.kronecker A B)).re ≤ 1 := by
  classical
  obtain ⟨hA1, hA2⟩ := hA
  obtain ⟨hB1, hB2⟩ := hB
  obtain ⟨L, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA1.nonneg
  obtain ⟨M, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB1.nonneg
  simp only [Matrix.star_eq_conjTranspose] at hA2 hB2 ⊢
  have hX : ∑ j, ‖PN_mv L (u j)‖ ^ 2 ≤ 1 := by
    have := PN_bessel L u hu; rw [hA2] at this; simpa using this
  have hY : ∑ j, ‖PN_mv M (v j)‖ ^ 2 ≤ 1 := by
    have := PN_bessel M v hv; rw [hB2] at this; simpa using this
  set x := fun j => PN_mv L (u j) with hx
  set y := fun j => PN_mv M (v j) with hy
  set T := ∑ j, tensorVec (x j) (y j) with hTdef
  have hT : ((‖T‖ ^ 2 : ℝ) : ℂ) = ∑ j, ∑ k, inner ℂ (x j) (x k) * inner ℂ (y j) (y k) := by
    have e : ((‖T‖ ^ 2 : ℝ) : ℂ) = inner ℂ T T := by
      rw [inner_self_eq_norm_sq_to_K]; norm_cast
    rw [e, hTdef]
    simp only [sum_inner, inner_sum, PN_inner_tensor]
    exact Finset.sum_comm
  have hF : PN_F u v (Matrix.kronecker (Lᴴ * L) (Mᴴ * M)) =
      (((∑ j, ‖x j‖ ^ 2) * (∑ k, ‖y k‖ ^ 2) - ‖T‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sub, hT, PN_F_apply]
    simp only [PN_qf_kron, PN_qf_gram]
    congr 1
    push_cast
    rw [Finset.sum_mul_sum]
    simp only [hx, hy, inner_self_eq_norm_sq_to_K]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by norm_cast
  rw [hF, Complex.ofReal_re]
  have hTn : ‖T‖ ≤ ∑ j, ‖x j‖ * ‖y j‖ :=
    (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => PN_tensor_norm _ _))
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖x j‖) (fun j => ‖y j‖)
  have hT2 : ‖T‖ ^ 2 ≤ (∑ j, ‖x j‖ * ‖y j‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hTn 2
  have hX0 : 0 ≤ ∑ j, ‖x j‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  have hY0 : 0 ≤ ∑ j, ‖y j‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  constructor
  · linarith
  · nlinarith [sq_nonneg ‖T‖, mul_le_mul hX hY hY0 zero_le_one]

lemma PN_sep_bound {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] {r : ℕ}
    (u : Fin r → EuclideanSpace ℂ I) (v : Fin r → EuclideanSpace ℂ J)
    (hu : Orthonormal ℂ u) (hv : Orthonormal ℂ v) (X : Matrix (I × J) (I × J) ℂ)
    (hX : IsSeparableDensity X) : 0 ≤ (PN_F u v X).re ∧ (PN_F u v X).re ≤ 1 := by
  obtain ⟨q, w, A, B, hw, hw1, hd, rfl⟩ := hX
  simp only [map_sum, map_smul, smul_eq_mul, Complex.re_sum, Complex.re_ofReal_mul]
  constructor
  · exact Finset.sum_nonneg fun j _ =>
      mul_nonneg (hw j) (PN_prod_bound u v hu hv _ _ (hd j).1 (hd j).2).1
  · calc _ ≤ ∑ j, w j * 1 := Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (PN_prod_bound u v hu hv _ _ (hd j).1 (hd j).2).2 (hw j)
      _ = 1 := by simp [hw1]

lemma PN_lower {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] {r : ℕ}
    (c : Fin r → ℝ) (u : Fin r → EuclideanSpace ℂ I) (v : Fin r → EuclideanSpace ℂ J)
    (hs : ∑ i, c i ^ 2 = 1) (hu : Orthonormal ℂ u) (hv : Orthonormal ℂ v) (ap am : ℝ)
    (rp rm : Matrix (I × J) (I × J) ℂ)
    (h : BaseDecomposition separableBase (pureDensity (schmidtState c u v)) ap am rp rm) :
    (∑ i, c i) ^ 2 - 1 ≤ am := by
  obtain ⟨hap, ham, hrp, hrm, heq⟩ := h
  have h1 := congrArg (fun X => (PN_F u v X).re) heq
  simp only [map_sub, map_smul, smul_eq_mul, Complex.sub_re, Complex.re_ofReal_mul,
    PN_F_rho c u v hu hv, Complex.ofReal_re, hs] at h1
  have b1 := PN_sep_bound u v hu hv rp hrp
  have b2 := PN_sep_bound u v hu hv rm hrm
  nlinarith [mul_nonneg hap b1.1, mul_le_mul_of_nonneg_left b2.2 ham]

def PN_z : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)

lemma PN_z_prim : IsPrimitiveRoot PN_z 3 := by
  have := Complex.isPrimitiveRoot_exp 3 (by norm_num)
  simpa [PN_z] using this

lemma PN_z_cm : conj PN_z * PN_z = 1 := by
  have h1 : ‖PN_z‖ = 1 := PN_z_prim.norm'_eq_one (by norm_num)
  rw [Complex.conj_mul', h1]; simp

lemma PN_z_conj : conj PN_z = PN_z ^ 2 := by
  have h3 : PN_z ^ 3 = 1 := PN_z_prim.pow_eq_one
  calc conj PN_z = conj PN_z * PN_z ^ 3 := by rw [h3, mul_one]
    _ = (conj PN_z * PN_z) * PN_z ^ 2 := by ring
    _ = _ := by rw [PN_z_cm, one_mul]

def PN_ph {r : ℕ} (θ : Fin r → Fin 3) (i : Fin r) : ℂ := PN_z ^ ((θ i : Fin 3) : ℕ)

lemma PN_ph_unit {r : ℕ} (θ : Fin r → Fin 3) (i : Fin r) : conj (PN_ph θ i) * PN_ph θ i = 1 := by
  rw [PN_ph, map_pow, ← mul_pow, PN_z_cm, one_pow]

lemma PN_z_succ (x : Fin 3) : PN_z ^ ((x + 1 : Fin 3) : ℕ) = PN_z ^ (x : ℕ) * PN_z := by
  have h3 : PN_z ^ 3 = 1 := PN_z_prim.pow_eq_one
  fin_cases x
  · simp
  · simp; ring
  · show PN_z ^ 0 = PN_z ^ 2 * PN_z
    rw [← pow_succ, h3, pow_zero]

lemma PN_ph_shift {r : ℕ} (θ : Fin r → Fin 3) (m n : Fin r) :
    PN_ph (θ + Pi.single m 1) n = PN_ph θ n * PN_z ^ (if n = m then 1 else 0) := by
  unfold PN_ph
  by_cases h : n = m
  · subst h; simp [PN_z_succ]
  · simp [h]

lemma PN_K {r : ℕ} (i j k l : Fin r) :
    ∑ θ : Fin r → Fin 3, PN_ph θ i * conj (PN_ph θ j) * conj (PN_ph θ k) * PN_ph θ l =
      if (i = j ∧ k = l) ∨ (i = k ∧ j = l) then (3 : ℂ) ^ r else 0 := by
  split_ifs with h
  · have hone : ∀ θ, PN_ph θ i * conj (PN_ph θ j) * conj (PN_ph θ k) * PN_ph θ l = 1 := by
      intro θ
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · calc _ = (conj (PN_ph θ i) * PN_ph θ i) * (conj (PN_ph θ k) * PN_ph θ k) := by ring
          _ = 1 := by rw [PN_ph_unit, PN_ph_unit, one_mul]
      · calc _ = (conj (PN_ph θ i) * PN_ph θ i) * (conj (PN_ph θ j) * PN_ph θ j) := by ring
          _ = 1 := by rw [PN_ph_unit, PN_ph_unit, one_mul]
    simp only [hone, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
    push_cast; ring
  · obtain ⟨m, hm⟩ : ∃ m : Fin r, (if i = m then 1 else 0) + (if l = m then 1 else 0) ≠
        (if j = m then 1 else 0) + (if k = m then (1 : ℕ) else 0) := by
      by_contra hcon
      push Not at hcon
      apply h
      have h1 := hcon i; have h2 := hcon j; have h3 := hcon k; have h4 := hcon l
      by_cases hij : i = j <;> by_cases hik : i = k <;> by_cases hil : i = l <;>
        by_cases hjk : j = k <;> by_cases hjl : j = l <;> by_cases hkl : k = l <;> simp_all
    set e : ℕ := (if i = m then 1 else 0) + 2 * (if j = m then 1 else 0) +
      2 * (if k = m then 1 else 0) + (if l = m then 1 else 0) with he_def
    have he : PN_z ^ e ≠ 1 := by
      rw [Ne, PN_z_prim.pow_eq_one_iff_dvd, he_def]
      split_ifs at hm ⊢ <;> omega
    set f : (Fin r → Fin 3) → ℂ :=
      fun θ => PN_ph θ i * conj (PN_ph θ j) * conj (PN_ph θ k) * PN_ph θ l with hf
    have hshift : ∀ θ, f (θ + Pi.single m 1) = f θ * PN_z ^ e := by
      intro θ
      simp only [hf, PN_ph_shift, map_mul, map_pow, PN_z_conj, he_def]
      ring
    have hsum : ∑ θ, f θ = (∑ θ, f θ) * PN_z ^ e := by
      rw [Finset.sum_mul, ← Equiv.sum_comp (Equiv.addRight (Pi.single m (1 : Fin 3))) f]
      exact Finset.sum_congr rfl fun θ _ => hshift θ
    have h0 : (∑ θ, f θ) * (1 - PN_z ^ e) = 0 := by rw [mul_sub, mul_one, ← hsum, sub_self]
    rcases mul_eq_zero.mp h0 with h0 | h0
    · exact h0
    · exact absurd (sub_eq_zero.mp h0).symm he

def PN_a {I : Type*} {r : ℕ} (c : Fin r → ℝ) (u : Fin r → EuclideanSpace ℂ I)
    (θ : Fin r → Fin 3) : EuclideanSpace ℂ I :=
  ∑ i, (((√(c i) : ℝ) : ℂ) * PN_ph θ i) • u i

def PN_b {J : Type*} {r : ℕ} (c : Fin r → ℝ) (v : Fin r → EuclideanSpace ℂ J)
    (θ : Fin r → Fin 3) : EuclideanSpace ℂ J :=
  ∑ j, (((√(c j) : ℝ) : ℂ) * conj (PN_ph θ j)) • v j

def PN_al {r : ℕ} (c : Fin r → ℝ) (θ : Fin r → Fin 3) (p : Fin r × Fin r) : ℂ :=
  ((√(c p.1) * √(c p.2) : ℝ) : ℂ) * (PN_ph θ p.1 * conj (PN_ph θ p.2))

def PN_w {r : ℕ} (c : Fin r → ℝ) (p : Fin r × Fin r) : ℝ :=
  if p.1 = p.2 then 0 else c p.1 * c p.2

lemma PN_ab {I J : Type*} {r : ℕ} (c : Fin r → ℝ) (u : Fin r → EuclideanSpace ℂ I)
    (v : Fin r → EuclideanSpace ℂ J) (θ : Fin r → Fin 3) :
    tensorVec (PN_a c u θ) (PN_b c v θ) = ∑ p, PN_al c θ p • tensorVec (u p.1) (v p.2) := by
  ext x
  simp only [tensorVec, PN_a, PN_b, PN_al, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Fintype.sum_prod_type, Finset.sum_mul_sum, PiLp.toLp_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  push_cast; ring

lemma PN_R_sum {K n : Type*} [Fintype K] (α β : K → ℂ) (e : K → EuclideanSpace ℂ n) :
    PN_R (∑ p, α p • e p) (∑ q, β q • e q) = ∑ p, ∑ q, (α p * conj (β q)) • PN_R (e p) (e q) := by
  ext x y
  simp only [PN_R, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, map_sum, map_mul,
    Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  ring

lemma PN_coef {r : ℕ} (c : Fin r → ℝ) (hc : ∀ i, 0 ≤ c i) (p q : Fin r × Fin r) :
    ∑ θ, PN_al c θ p * conj (PN_al c θ q) =
      (3 : ℂ) ^ r * (if p.1 = p.2 ∧ q.1 = q.2 then ((c p.1 * c q.1 : ℝ) : ℂ) else 0) +
      (3 : ℂ) ^ r * (if p = q then ((PN_w c p : ℝ) : ℂ) else 0) := by
  have h1 : ∀ θ, PN_al c θ p * conj (PN_al c θ q) =
      ((√(c p.1) * √(c p.2) * (√(c q.1) * √(c q.2)) : ℝ) : ℂ) *
        (PN_ph θ p.1 * conj (PN_ph θ p.2) * conj (PN_ph θ q.1) * PN_ph θ q.2) := by
    intro θ
    simp only [PN_al, map_mul, Complex.conj_ofReal, Complex.conj_conj]
    push_cast; ring
  simp only [h1]
  rw [← Finset.mul_sum, PN_K]
  obtain ⟨i, j⟩ := p
  obtain ⟨k, l⟩ := q
  simp only [PN_w, Prod.mk.injEq]
  have sq : ∀ a, 0 ≤ a → √a * √a = a := fun a ha => Real.mul_self_sqrt ha
  by_cases hij : i = j
  · subst hij
    by_cases hkl : k = l
    · subst hkl
      simp only [true_or, if_true, and_self]
      rw [show √(c i) * √(c i) * (√(c k) * √(c k)) = c i * c k by rw [sq _ (hc i), sq _ (hc k)]]
      split_ifs <;> push_cast <;> ring
    · simp only [hkl, and_false, false_or, if_false, mul_zero, zero_add]
      split_ifs with h
      · obtain ⟨rfl, rfl⟩ := h; exact absurd rfl hkl
      · simp
  · simp only [hij, false_and, false_or, if_false, mul_zero, zero_add]
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h
      rw [show √(c i) * √(c j) * (√(c i) * √(c j)) = c i * c j by
        rw [show √(c i) * √(c j) * (√(c i) * √(c j)) = (√(c i) * √(c i)) * (√(c j) * √(c j)) by
          ring, sq _ (hc i), sq _ (hc j)]]
      push_cast; ring
    · simp

lemma PN_diag_sum {r : ℕ} {M : Type*} [AddCommMonoid M] (g : Fin r × Fin r → M) :
    ∑ p, (if p.1 = p.2 then g p else 0) = ∑ i, g (i, i) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

lemma PN_avg {I J : Type*} [Fintype I] [Fintype J] {r : ℕ} (c : Fin r → ℝ) (hc : ∀ i, 0 ≤ c i)
    (u : Fin r → EuclideanSpace ℂ I) (v : Fin r → EuclideanSpace ℂ J) :
    ∑ θ, pureDensity (tensorVec (PN_a c u θ) (PN_b c v θ)) =
      (3 : ℂ) ^ r • (pureDensity (schmidtState c u v) +
        ∑ p, ((PN_w c p : ℝ) : ℂ) • pureDensity (tensorVec (u p.1) (v p.2))) := by
  set e : Fin r × Fin r → EuclideanSpace ℂ (I × J) := fun p => tensorVec (u p.1) (v p.2) with he
  have h1 : ∀ θ, pureDensity (tensorVec (PN_a c u θ) (PN_b c v θ)) =
      ∑ p, ∑ q, (PN_al c θ p * conj (PN_al c θ q)) • PN_R (e p) (e q) := by
    intro θ
    rw [PN_ab]
    exact PN_R_sum _ _ e
  simp only [h1]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun p _ => Finset.sum_comm]
  simp only [← Finset.sum_smul]
  simp only [PN_coef c hc, add_smul, Finset.sum_add_distrib, mul_smul,
    ← Finset.smul_sum, smul_add]
  congr 2
  · have hψ : schmidtState c u v = ∑ i, (c i : ℂ) • e (i, i) := rfl
    show _ = PN_R (schmidtState c u v) (schmidtState c u v)
    rw [hψ, PN_R_sum]
    calc _ = ∑ p, (if p.1 = p.2 then ∑ q, (if q.1 = q.2 then
          ((c p.1 * c q.1 : ℝ) : ℂ) • PN_R (e p) (e q) else 0) else 0) := by
          refine Finset.sum_congr rfl fun p _ => ?_
          by_cases hp : p.1 = p.2
          · rw [if_pos hp]
            refine Finset.sum_congr rfl fun q _ => ?_
            by_cases hq : q.1 = q.2 <;> simp [hp, hq]
          · simp [hp]
      _ = _ := by
          rw [PN_diag_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [PN_diag_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          simp
  · refine Finset.sum_congr rfl fun p _ => ?_
    simp [ite_smul]
    rfl

lemma PN_pd_psd {n : Type*} [Fintype n] (ψ : EuclideanSpace ℂ n) : (pureDensity ψ).PosSemidef := by
  have := Matrix.posSemidef_vecMulVec_self_star (ψ.ofLp)
  convert this using 1
  ext a b; simp [pureDensity, Matrix.vecMulVec]

lemma PN_dens {n : Type*} [Fintype n] (ψ : EuclideanSpace ℂ n) (t : ℝ) (ht : 0 < t)
    (h : inner ℂ ψ ψ = (t : ℂ)) : IsDensityMatrix (((t⁻¹ : ℝ) : ℂ) • pureDensity ψ) := by
  refine ⟨(PN_pd_psd ψ).smul (Complex.zero_le_real.mpr (inv_nonneg.mpr ht.le)), ?_⟩
  rw [Matrix.trace_smul, show (pureDensity ψ).trace = inner ℂ ψ ψ from PN_R_trace ψ ψ, h,
    smul_eq_mul, ← Complex.ofReal_mul, inv_mul_cancel₀ ht.ne', Complex.ofReal_one]

lemma PN_dens_unit {n : Type*} [Fintype n] (ψ : EuclideanSpace ℂ n) (h : ‖ψ‖ = 1) :
    IsDensityMatrix (pureDensity ψ) := by
  have h1 : inner ℂ ψ ψ = ((1 : ℝ) : ℂ) := by rw [inner_self_eq_norm_sq_to_K, h]; simp
  have := PN_dens ψ 1 one_pos h1
  simpa using this

lemma PN_kron_pd {I J : Type*} (a : EuclideanSpace ℂ I) (b : EuclideanSpace ℂ J) :
    Matrix.kronecker (pureDensity a) (pureDensity b) = pureDensity (tensorVec a b) := by
  ext p q
  simp [pureDensity, tensorVec, Matrix.kronecker, Matrix.kroneckerMap_apply]
  ring

lemma PN_kron_smul {I J : Type*} (a b : ℂ) (P : Matrix I I ℂ) (Q : Matrix J J ℂ) :
    Matrix.kronecker (a • P) (b • Q) = (a * b) • Matrix.kronecker P Q := by
  ext p q
  simp [Matrix.kronecker, Matrix.kroneckerMap_apply]
  ring

lemma PN_sep_of {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] {K : Type*}
    [Fintype K] (w : K → ℝ) (A : K → Matrix I I ℂ) (B : K → Matrix J J ℂ) (hw : ∀ k, 0 ≤ w k)
    (h1 : ∑ k, w k = 1) (hd : ∀ k, IsDensityMatrix (A k) ∧ IsDensityMatrix (B k)) :
    IsSeparableDensity (∑ k, (w k : ℂ) • Matrix.kronecker (A k) (B k)) := by
  classical
  let e := Fintype.equivFin K
  refine ⟨Fintype.card K, fun s => w (e.symm s), fun s => A (e.symm s), fun s => B (e.symm s),
    fun s => hw _, ?_, fun s => hd _, ?_⟩
  · rw [Equiv.sum_comp e.symm w]; exact h1
  · exact (Equiv.sum_comp e.symm (fun k => (w k : ℂ) • Matrix.kronecker (A k) (B k))).symm

lemma PN_w_nonneg {r : ℕ} (c : Fin r → ℝ) (hc : ∀ i, 0 ≤ c i) (p : Fin r × Fin r) :
    0 ≤ PN_w c p := by
  unfold PN_w; split_ifs
  · exact le_refl _
  · exact mul_nonneg (hc _) (hc _)

lemma PN_wsum {r : ℕ} (c : Fin r → ℝ) (hs : ∑ i, c i ^ 2 = 1) :
    ∑ p, PN_w c p = (∑ i, c i) ^ 2 - 1 := by
  have : ∀ p : Fin r × Fin r, PN_w c p = c p.1 * c p.2 - (if p.1 = p.2 then c p.1 * c p.2 else 0) := by
    intro p; unfold PN_w; split_ifs <;> ring
  simp only [this, Finset.sum_sub_distrib, PN_diag_sum]
  rw [sq, Finset.sum_mul_sum, Fintype.sum_prod_type, ← hs]
  simp [sq]

lemma PN_a_inner {I : Type*} [Fintype I] {r : ℕ} (c : Fin r → ℝ) (hc : ∀ i, 0 ≤ c i)
    (u : Fin r → EuclideanSpace ℂ I) (hu : Orthonormal ℂ u) (θ : Fin r → Fin 3) :
    inner ℂ (PN_a c u θ) (PN_a c u θ) = ((∑ i, c i : ℝ) : ℂ) := by
  rw [PN_a, hu.inner_sum]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, Complex.conj_ofReal,
    show (√(c i) : ℂ) * conj (PN_ph θ i) * ((√(c i) : ℂ) * PN_ph θ i) =
      ((√(c i) * √(c i) : ℝ) : ℂ) * (conj (PN_ph θ i) * PN_ph θ i) by push_cast; ring,
    PN_ph_unit, Real.mul_self_sqrt (hc i)]
  simp

lemma PN_b_inner {J : Type*} [Fintype J] {r : ℕ} (c : Fin r → ℝ) (hc : ∀ i, 0 ≤ c i)
    (v : Fin r → EuclideanSpace ℂ J) (hv : Orthonormal ℂ v) (θ : Fin r → Fin 3) :
    inner ℂ (PN_b c v θ) (PN_b c v θ) = ((∑ i, c i : ℝ) : ℂ) := by
  rw [PN_b, hv.inner_sum]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, Complex.conj_ofReal, Complex.conj_conj,
    show (√(c i) : ℂ) * PN_ph θ i * ((√(c i) : ℂ) * conj (PN_ph θ i)) =
      ((√(c i) * √(c i) : ℝ) : ℂ) * (conj (PN_ph θ i) * PN_ph θ i) by push_cast; ring,
    PN_ph_unit, Real.mul_self_sqrt (hc i)]
  simp

lemma PN_upper {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] {r : ℕ}
    (c : Fin r → ℝ) (u : Fin r → EuclideanSpace ℂ I) (v : Fin r → EuclideanSpace ℂ J)
    (hc : ∀ i, 0 ≤ c i) (hs : ∑ i, c i ^ 2 = 1) (hu : Orthonormal ℂ u) (hv : Orthonormal ℂ v) :
    ∃ ap rp rm, BaseDecomposition separableBase (pureDensity (schmidtState c u v)) ap
      ((∑ i, c i) ^ 2 - 1) rp rm := by
  set S := ∑ i, c i with hSdef
  have hw0 := PN_w_nonneg c hc
  have hws := PN_wsum c hs
  have hS1 : 0 ≤ S ^ 2 - 1 := by rw [← hws]; exact Finset.sum_nonneg fun p _ => hw0 p
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => hc i
  have hS : 0 < S := by
    rcases hS0.lt_or_eq with h | h
    · exact h
    · rw [← h] at hS1; norm_num at hS1
  set D : Matrix (I × J) (I × J) ℂ :=
    ∑ p, ((PN_w c p : ℝ) : ℂ) • pureDensity (tensorVec (u p.1) (v p.2)) with hD
  set σp : Matrix (I × J) (I × J) ℂ := ∑ θ : Fin r → Fin 3, (((1 / 3 ^ r : ℝ)) : ℂ) •
    Matrix.kronecker (((S⁻¹ : ℝ) : ℂ) • pureDensity (PN_a c u θ))
      (((S⁻¹ : ℝ) : ℂ) • pureDensity (PN_b c v θ)) with hσp
  have hσp_sep : IsSeparableDensity σp := by
    refine PN_sep_of (fun _ => 1 / 3 ^ r) _ _ (fun _ => by positivity) ?_ fun θ =>
      ⟨PN_dens _ S hS (PN_a_inner c hc u hu θ), PN_dens _ S hS (PN_b_inner c hc v hv θ)⟩
    simp [Finset.sum_const]
  have hσp_eq : ((S ^ 2 : ℝ) : ℂ) • σp = pureDensity (schmidtState c u v) + D := by
    simp only [hσp, PN_kron_smul, smul_smul, PN_kron_pd]
    rw [← Finset.smul_sum, PN_avg c hc u v]
    rw [← hD]
    simp only [smul_smul]
    have key : ∀ (k : ℂ) (Y : Matrix (I × J) (I × J) ℂ), k = 1 → k • Y = Y := by
      intro k Y hk; rw [hk, one_smul]
    apply key
    push_cast
    field_simp
  refine ⟨S ^ 2, ?_⟩
  by_cases hz : S ^ 2 - 1 = 0
  · have hD0 : D = 0 := by
      have : ∀ p ∈ Finset.univ, PN_w c p = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg fun p _ => hw0 p).mp (hws.trans hz)
      simp [hD, this]
    refine ⟨σp, σp, sq_nonneg _, le_of_eq hz.symm, hσp_sep, hσp_sep, ?_⟩
    rw [hσp_eq, hD0, hz]; simp
  · have hpos : 0 < S ^ 2 - 1 := lt_of_le_of_ne hS1 (Ne.symm hz)
    set σm : Matrix (I × J) (I × J) ℂ := ∑ p, ((PN_w c p / (S ^ 2 - 1) : ℝ) : ℂ) •
      Matrix.kronecker (pureDensity (u p.1)) (pureDensity (v p.2)) with hσm
    have hσm_sep : IsSeparableDensity σm := by
      refine PN_sep_of (fun p => PN_w c p / (S ^ 2 - 1)) _ _
        (fun p => div_nonneg (hw0 p) hpos.le) ?_ fun p =>
          ⟨PN_dens_unit _ (hu.1 _), PN_dens_unit _ (hv.1 _)⟩
      rw [← Finset.sum_div, hws, div_self hz]
    have hσm_eq : (((S ^ 2 - 1 : ℝ)) : ℂ) • σm = D := by
      simp only [hσm, hD, Finset.smul_sum, smul_smul, PN_kron_pd]
      refine Finset.sum_congr rfl fun p _ => ?_
      congr 1
      rw [← Complex.ofReal_mul, mul_div_cancel₀ _ hz]
    refine ⟨σp, σm, sq_nonneg _, hS1, hσp_sep, hσm_sep, ?_⟩
    rw [show ((S ^ 2 : ℝ) : ℂ) = ((S ^ 2 : ℝ) : ℂ) from rfl, hσp_eq,
      show (((S ^ 2 - 1 : ℝ)) : ℂ) • σm = D from hσm_eq]
    simp

lemma PN_main {I J : Type*} [Fintype I] [Fintype J]
    [Nonempty I] [Nonempty J] [DecidableEq I] [DecidableEq J]
    {r : ℕ} (c : Fin r → ℝ) (u : Fin r → EuclideanSpace ℂ I)
    (v : Fin r → EuclideanSpace ℂ J) (hc : ∀ i, 0 ≤ c i)
    (hs : ∑ i, c i^2 = 1) (hu : Orthonormal ℂ u) (hv : Orthonormal ℂ v) :
    negativity (pureDensity (schmidtState c u v)) = ((∑ i, c i)^2-1)/2 ∧
      separableRobustness (pureDensity (schmidtState c u v)) =
        2*negativity (pureDensity (schmidtState c u v)) := by
  have hneg : negativity (pureDensity (schmidtState c u v)) = ((∑ i, c i)^2-1)/2 := by
    rw [negativity, PN_tn c u v hc hu hv]
  refine ⟨hneg, ?_⟩
  rw [hneg]
  have : separableRobustness (pureDensity (schmidtState c u v)) = (∑ i, c i)^2 - 1 := by
    unfold separableRobustness baseNeg
    apply IsLeast.csInf_eq
    refine ⟨?_, ?_⟩
    · obtain ⟨ap, rp, rm, h⟩ := PN_upper c u v hc hs hu hv
      exact ⟨ap, _, rp, rm, h, rfl⟩
    · rintro x ⟨ap, am, rp, rm, h, hx⟩
      rw [hx]
      exact PN_lower c u v hs hu hv ap am rp rm h
  rw [this]; ring

end QAlgorithms.Papers.Independent.Independent1.P07

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

open QAlgorithms QAlgorithms.Entanglement QAlgorithms.Papers.Independent.Independent1.P07 in
/-- Proposition 8, Eq. (48), PDF p. 7, including the robustness relation attributed to [18]. -/
theorem solution {I J : Type*} [Fintype I] [Fintype J]
    [Nonempty I] [Nonempty J] [DecidableEq I] [DecidableEq J]
    {r : ℕ} (c : Fin r → ℝ) (u : Fin r → EuclideanSpace ℂ I)
    (v : Fin r → EuclideanSpace ℂ J) (hc : ∀ i, 0 ≤ c i)
    (hs : ∑ i, c i^2 = 1) (hu : Orthonormal ℂ u) (hv : Orthonormal ℂ v) :
    let rho := pureDensity (schmidtState c u v)
    negativity rho = ((∑ i, c i)^2-1)/2 ∧ separableRobustness rho = 2*negativity rho := by
  intro rho
  exact PN_main c u v hc hs hu hv

