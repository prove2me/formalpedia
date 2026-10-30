-- Prove2me | solution 1 for RobustPCA.Recovery.theorem_2_6
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-29T12:13:09.902593+00:00
-- url     : https://prove2.me/submissions/3d9166bd-473f-493f-a928-fd6e5adb96be

import Mathlib
import Definitions.Def_RobustPCA_Recovery_Setup
import Theorems.Thm_IntroMatrixConc_Sampling_corollary_6_1_2

set_option autoImplicit false

open MatrixCompletion

namespace RPCA26

open RobustPCA.Recovery
open scoped BigOperators Classical


/-! ## Projection algebra (copied from scratch/decomp/429b6866 and 0363db4b) -/

noncomputable def projM {n r : ℕ} (u : Fin r → Fin n → ℝ) : RealMatrix n n :=
  fun i a => ∑ k, u k i * u k a

noncomputable def PU {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) : RealMatrix n n :=
  projM SV.u

noncomputable def PV {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) : RealMatrix n n :=
  projM SV.v

lemma orth_idem {n r : ℕ} (u : Fin r → Fin n → ℝ)
    (hu : ∀ k l, ∑ i, u k i * u l i = if k = l then 1 else 0) :
    projM u * projM u = projM u := by
  ext i c
  simp only [Matrix.mul_apply, projM]
  have h1 : ∀ a, (∑ k, u k i * u k a) * (∑ l, u l a * u l c) =
      ∑ k, ∑ l, u k i * u l c * (u k a * u l a) := by
    intro a
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    ring
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.sum_comm]
  have h2 : ∀ l, ∑ a, u k i * u l c * (u k a * u l a) =
      u k i * u l c * (if k = l then 1 else 0) := by
    intro l
    rw [← Finset.mul_sum, hu]
  simp_rw [h2]
  simp

lemma PU_idem {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) : PU SV * PU SV = PU SV :=
  orth_idem SV.u SV.u_orthonormal

lemma PV_idem {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) : PV SV * PV SV = PV SV :=
  orth_idem SV.v SV.v_orthonormal

lemma projM_transpose {n r : ℕ} (u : Fin r → Fin n → ℝ) :
    Matrix.transpose (projM u) = projM u := by
  ext i a
  simp only [Matrix.transpose_apply, projM]
  exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)

lemma tangent_eq {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (X : RealMatrix n n) :
    tangentProjection SV X = PU SV * X + X * PV SV - PU SV * X * PV SV := by
  ext i j
  simp only [tangentProjection, leftSingularProjection, rightSingularProjection,
    twoSidedSingularProjection, Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply, PU, PV, projM]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Finset.sum_mul]

lemma tangent_add {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (X Y : RealMatrix n n) :
    tangentProjection SV (X + Y) = tangentProjection SV X + tangentProjection SV Y := by
  simp only [tangent_eq, Matrix.mul_add, Matrix.add_mul]
  abel

lemma tangent_sub {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (X Y : RealMatrix n n) :
    tangentProjection SV (X - Y) = tangentProjection SV X - tangentProjection SV Y := by
  simp only [tangent_eq, Matrix.mul_sub, Matrix.sub_mul]
  abel

lemma tangent_smul {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (c : ℝ) (X : RealMatrix n n) :
    tangentProjection SV (c • X) = c • tangentProjection SV X := by
  simp only [tangent_eq, Matrix.mul_smul, Matrix.smul_mul, smul_sub, smul_add]

lemma tangent_idem {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (X : RealMatrix n n) :
    tangentProjection SV (tangentProjection SV X) = tangentProjection SV X := by
  have hA := PU_idem SV
  have hB := PV_idem SV
  have hB' : ∀ Y : RealMatrix n n, Y * PV SV * PV SV = Y * PV SV := by
    intro Y; rw [Matrix.mul_assoc, hB]
  simp only [tangent_eq, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul,
    ← Matrix.mul_assoc, hA, hB']
  abel

lemma entrySup_nonneg {n : ℕ} (A : RealMatrix n n) : 0 ≤ entrySupNorm A := by
  unfold entrySupNorm
  exact Real.iSup_nonneg (fun i => Real.iSup_nonneg (fun j => abs_nonneg _))

lemma le_entrySup {n : ℕ} (A : RealMatrix n n) (i j : Fin n) : |A i j| ≤ entrySupNorm A := by
  unfold entrySupNorm
  exact le_ciSup_of_le (Finite.bddAbove_range _) i
    (le_ciSup (f := fun j => |A i j|) (Finite.bddAbove_range _) j)

lemma entrySup_add {n : ℕ} (A B : RealMatrix n n) :
    entrySupNorm (A + B) ≤ entrySupNorm A + entrySupNorm B := by
  have h0 : 0 ≤ entrySupNorm A + entrySupNorm B :=
    add_nonneg (entrySup_nonneg A) (entrySup_nonneg B)
  unfold entrySupNorm
  refine Real.iSup_le (fun i => Real.iSup_le (fun j => ?_) h0) h0
  calc |(A + B) i j| = |A i j + B i j| := rfl
    _ ≤ |A i j| + |B i j| := abs_add_le _ _
    _ ≤ entrySupNorm A + entrySupNorm B := add_le_add (le_entrySup A i j) (le_entrySup B i j)

lemma entrySup_le {n : ℕ} (A : RealMatrix n n) (b : ℝ) (hb : 0 ≤ b)
    (h : ∀ i j, |A i j| ≤ b) : entrySupNorm A ≤ b := by
  unfold entrySupNorm
  exact Real.iSup_le (fun i => Real.iSup_le (fun j => h i j) hb) hb

/-! ## Bernoulli sums -/

lemma bw_sum_one {N : ℕ} (p : ℝ) :
    ∑ A : Finset (Fin N × Fin N), bernoulliObservationWeight p A = 1 := by
  have h := Finset.sum_pow_mul_eq_add_pow p (1 - p) (Finset.univ : Finset (Fin N × Fin N))
  rw [Finset.powerset_univ, Finset.card_univ, show p + (1 - p) = 1 by ring, one_pow] at h
  exact h

lemma bw_nonneg {N : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (A : Finset (Fin N × Fin N)) :
    0 ≤ bernoulliObservationWeight p A := by
  unfold bernoulliObservationWeight
  exact mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _)

lemma bep_not {N : ℕ} (p : ℝ) (P : Finset (Fin N × Fin N) → Prop) :
    bernoulliEventProb p (fun B => ¬ P B) = 1 - bernoulliEventProb p P := by
  unfold bernoulliEventProb
  rw [← bw_sum_one (N := N) p, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun B _ => ?_)
  by_cases h : P B
  · rw [if_neg (not_not.mpr h), if_pos h]; ring
  · rw [if_pos h, if_neg h]; ring

lemma entrySup_zero {n : ℕ} : entrySupNorm (0 : RealMatrix n n) = 0 :=
  le_antisymm (entrySup_le _ 0 le_rfl (fun i j => by simp)) (entrySup_nonneg _)

lemma prod_ite_univ {α : Type*} [Fintype α] [DecidableEq α] (B : Finset α) (a b : ℝ) :
    ∏ x, (if x ∈ B then a else b) = a ^ B.card * b ^ (Fintype.card α - B.card) := by
  rw [← Finset.prod_mul_prod_compl B]
  have h1 : ∏ x ∈ B, (if x ∈ B then a else b) = ∏ x ∈ B, a :=
    Finset.prod_congr rfl (fun x hx => by simp [hx])
  have h2 : ∏ x ∈ Bᶜ, (if x ∈ B then a else b) = ∏ x ∈ Bᶜ, b :=
    Finset.prod_congr rfl (fun x hx => by rw [Finset.mem_compl] at hx; simp [hx])
  rw [h1, h2, Finset.prod_const, Finset.prod_const, Finset.card_compl]

lemma bw_eq_prod {N : ℕ} (p : ℝ) (A : Finset (Fin N × Fin N)) :
    bernoulliObservationWeight p A = ∏ x, (if x ∈ A then p else 1 - p) := by
  unfold bernoulliObservationWeight
  rw [prod_ite_univ]

/-! ## Frobenius inner product and the coordinate form of `P_T` -/

lemma inner_eq_trace {n : ℕ} (X Y : RealMatrix n n) :
    matrixInner X Y = (Matrix.transpose X * Y).trace := by
  simp only [matrixInner, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]

lemma inner_tangent {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (X Y : RealMatrix n n) :
    matrixInner (tangentProjection SV X) Y = matrixInner X (tangentProjection SV Y) := by
  rw [inner_eq_trace, inner_eq_trace, tangent_eq, tangent_eq]
  have hU : Matrix.transpose (PU SV) = PU SV := projM_transpose _
  have hV : Matrix.transpose (PV SV) = PV SV := projM_transpose _
  simp only [Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_mul, hU, hV,
    Matrix.sub_mul, Matrix.add_mul, Matrix.mul_sub, Matrix.mul_add, Matrix.trace_sub,
    Matrix.trace_add, Matrix.mul_assoc]
  have e1 : (PV SV * (Matrix.transpose X * Y)).trace =
      (Matrix.transpose X * (Y * PV SV)).trace := by
    rw [Matrix.trace_mul_comm, Matrix.mul_assoc]
  have e2 : (PV SV * (Matrix.transpose X * (PU SV * Y))).trace =
      (Matrix.transpose X * (PU SV * (Y * PV SV))).trace := by
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [e1, e2]

lemma inner_coord {n : ℕ} (a b : Fin n) (M : RealMatrix n n) :
    matrixInner (coordinateMatrix a b) M = M a b := by
  unfold matrixInner coordinateMatrix
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · simp
    · intro j _ hj; simp [hj]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro i _ hi
    apply Finset.sum_eq_zero; intro j _; simp [hi]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma inner_coord' {n : ℕ} (a b : Fin n) (M : RealMatrix n n) :
    ∑ i, ∑ j, M i j * coordinateMatrix a b i j = M a b := by
  rw [← inner_coord a b M]
  unfold matrixInner
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => mul_comm _ _))

/-- `P_T e_ab`, the coefficient matrix of the entry `(a, b)` of `P_T`. -/
noncomputable def Ecoef {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (a b : Fin n) :
    RealMatrix n n :=
  tangentProjection SV (coordinateMatrix a b)

lemma tangent_entry {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (Y : RealMatrix n n)
    (a b : Fin n) : tangentProjection SV Y a b = ∑ i, ∑ j, Ecoef SV a b i j * Y i j := by
  rw [← inner_coord a b (tangentProjection SV Y), ← inner_tangent]
  rfl

lemma Ecoef_sq {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (a b : Fin n) :
    ∑ i, ∑ j, Ecoef SV a b i j ^ 2 = Ecoef SV a b a b := by
  have h := tangent_entry SV (Ecoef SV a b) a b
  rw [Ecoef, tangent_idem] at h
  rw [Ecoef, h]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

lemma Ecoef_self {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (a b i j : Fin n) :
    Ecoef SV a b i j = ∑ x, ∑ y, Ecoef SV i j x y * Ecoef SV a b x y := by
  have h := tangent_entry SV (Ecoef SV a b) i j
  rw [Ecoef, tangent_idem] at h
  rw [Ecoef, h]

lemma Ecoef_diag {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (a b : Fin n) :
    Ecoef SV a b a b = PU SV a a + PV SV b b - PU SV a a * PV SV b b := by
  rw [Ecoef, tangent_eq]
  simp [Matrix.mul_apply, coordinateMatrix, Matrix.sub_apply, Matrix.add_apply, ite_and]

lemma PU_diag {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (a : Fin n) :
    PU SV a a = ∑ k, SV.u k a ^ 2 := by
  unfold PU projM
  exact Finset.sum_congr rfl (fun k _ => by ring)

lemma PV_diag {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (b : Fin n) :
    PV SV b b = ∑ k, SV.v k b ^ 2 := by
  unfold PV projM
  exact Finset.sum_congr rfl (fun k _ => by ring)

lemma Ecoef_sq_le {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (μ : ℝ)
    (hinc : Incoherent SV μ) (a b : Fin n) :
    ∑ i, ∑ j, Ecoef SV a b i j ^ 2 ≤ 2 * μ * r / n := by
  rw [Ecoef_sq, Ecoef_diag, PU_diag, PV_diag]
  have h1 := hinc.1 a
  have h2 := hinc.2.1 b
  have h3 : 0 ≤ ∑ k, SV.u k a ^ 2 := Finset.sum_nonneg (fun k _ => sq_nonneg _)
  have h4 : 0 ≤ ∑ k, SV.v k b ^ 2 := Finset.sum_nonneg (fun k _ => sq_nonneg _)
  have h5 := mul_nonneg h3 h4
  have e : 2 * μ * r / n = μ * r / n + μ * r / n := by ring
  rw [e]
  linarith


lemma mu_ge_one {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (μ : ℝ) (hn : 0 < n) (hr : 0 < r)
    (hinc : Incoherent SV μ) : 1 ≤ μ := by
  have hsum : ∑ i : Fin n, ∑ k, (SV.u k i) ^ 2 = r := by
    simp only [sq]
    rw [Finset.sum_comm]
    simp [SV.u_orthonormal]
  have hle : ∑ i : Fin n, ∑ k, (SV.u k i) ^ 2 ≤ ∑ _i : Fin n, μ * r / n :=
    Finset.sum_le_sum (fun i _ => hinc.1 i)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hsum] at hle
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have e : (n : ℝ) * (μ * r / n) = μ * r := by field_simp
  rw [e] at hle
  by_contra hc
  push Not at hc
  nlinarith

/-! ## Vectorization of `n × n` matrices -/

def eqv (n : ℕ) : Fin (n * n) ≃ Fin n × Fin n := finProdFinEquiv.symm

def vecR {n : ℕ} (X : RealMatrix n n) : Fin (n * n) → ℝ :=
  fun m => X (eqv n m).1 (eqv n m).2

def unvec {n : ℕ} (u : Fin (n * n) → ℝ) : RealMatrix n n :=
  fun i j => u ((eqv n).symm (i, j))

lemma vecR_unvec {n : ℕ} (u : Fin (n * n) → ℝ) : vecR (unvec u) = u := by
  funext m
  simp [vecR, unvec]

lemma sum_eqv {n : ℕ} (f : Fin n × Fin n → ℝ) :
    ∑ m : Fin (n * n), f (eqv n m) = ∑ i, ∑ j, f (i, j) := by
  rw [Equiv.sum_comp (eqv n) f, Fintype.sum_prod_type]

lemma sumsq_vecR {n : ℕ} (X : RealMatrix n n) : ∑ m, vecR X m ^ 2 = frobeniusNormSq X := by
  unfold vecR frobeniusNormSq
  exact sum_eqv (fun p => X p.1 p.2 ^ 2)

lemma Ecoef_symm {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (a b i j : Fin n) :
    Ecoef SV a b i j = Ecoef SV i j a b := by
  rw [Ecoef_self SV a b i j, Ecoef_self SV i j a b]
  exact Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => mul_comm _ _))

/-- `vec(P_T e_k)`. -/
noncomputable def avec {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (k : Fin (n * n)) :
    Fin (n * n) → ℝ :=
  vecR (Ecoef SV (eqv n k).1 (eqv n k).2)

lemma avec_sq_le {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (μ : ℝ)
    (hinc : Incoherent SV μ) (k : Fin (n * n)) :
    ∑ m, avec SV k m ^ 2 ≤ 2 * μ * r / n := by
  unfold avec
  rw [sumsq_vecR]
  exact Ecoef_sq_le SV μ hinc _ _

/-- The real `n² × n²` matrix `∑_k c_k vec(P_T e_k) vec(P_T e_k)ᵀ`. -/
noncomputable def Bop {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (c : Fin (n * n) → ℝ) :
    Matrix (Fin (n * n)) (Fin (n * n)) ℝ :=
  ∑ k, c k • Matrix.vecMulVec (avec SV k) (avec SV k)

/-- Entrywise weighting `(C ∘ Y)_{ij} = c_{(i,j)} Y_{ij}`. -/
def cw {n : ℕ} (c : Fin (n * n) → ℝ) (Y : RealMatrix n n) : RealMatrix n n :=
  fun i j => c ((eqv n).symm (i, j)) * Y i j

lemma Bop_mulVec_apply {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (c : Fin (n * n) → ℝ)
    (v : Fin (n * n) → ℝ) (m : Fin (n * n)) :
    Matrix.mulVec (Bop SV c) v m = ∑ k, c k * avec SV k m * ∑ m', avec SV k m' * v m' := by
  simp only [Bop, Matrix.mulVec, dotProduct, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun m' _ => ?_))
  ring

lemma Bop_vec {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (c : Fin (n * n) → ℝ)
    (X : RealMatrix n n) :
    Matrix.mulVec (Bop SV c) (vecR X) =
      vecR (tangentProjection SV (cw c (tangentProjection SV X))) := by
  funext m
  rw [Bop_mulVec_apply]
  have h1 : ∀ k, ∑ m', avec SV k m' * vecR X m' =
      tangentProjection SV X (eqv n k).1 (eqv n k).2 := by
    intro k
    rw [tangent_entry]
    unfold avec vecR
    exact sum_eqv (fun p => Ecoef SV (eqv n k).1 (eqv n k).2 p.1 p.2 * X p.1 p.2)
  simp_rw [h1]
  show _ = tangentProjection SV (cw c (tangentProjection SV X)) (eqv n m).1 (eqv n m).2
  rw [tangent_entry]
  rw [← sum_eqv (n := n) (fun p => Ecoef SV (eqv n m).1 (eqv n m).2 p.1 p.2 *
    cw c (tangentProjection SV X) p.1 p.2)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [avec, vecR, cw, Prod.mk.eta, Equiv.symm_apply_apply]
  rw [Ecoef_symm SV (eqv n k).1 (eqv n k).2 (eqv n m).1 (eqv n m).2]
  ring

lemma frobSq_nonneg {n : ℕ} (X : RealMatrix n n) : 0 ≤ frobeniusNormSq X := by
  unfold frobeniusNormSq; positivity

lemma frobSq_T_le {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (X : RealMatrix n n) :
    frobeniusNormSq (tangentProjection SV X) ≤ frobeniusNormSq X := by
  have hYY : matrixInner (tangentProjection SV X) (tangentProjection SV X) =
      matrixInner X (tangentProjection SV X) := by
    rw [inner_tangent, tangent_idem]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n × Fin n))
    (fun p => X p.1 p.2) (fun p => tangentProjection SV X p.1 p.2)
  simp only [Fintype.sum_prod_type] at hcs
  have e1 : (∑ i, ∑ j, X i j * tangentProjection SV X i j) =
      frobeniusNormSq (tangentProjection SV X) := by
    have : frobeniusNormSq (tangentProjection SV X) =
        matrixInner (tangentProjection SV X) (tangentProjection SV X) := by
      simp only [frobeniusNormSq, matrixInner, sq]
    rw [this, hYY]; rfl
  have e2 : (∑ i, ∑ j, X i j ^ 2) = frobeniusNormSq X := rfl
  have e3 : (∑ i, ∑ j, tangentProjection SV X i j ^ 2) =
      frobeniusNormSq (tangentProjection SV X) := rfl
  rw [e1, e2, e3] at hcs
  have h0 := frobSq_nonneg (tangentProjection SV X)
  have h1 := frobSq_nonneg X
  nlinarith

lemma frobSq_cw_le {n : ℕ} (c : Fin (n * n) → ℝ) (K : ℝ) (hc : ∀ k, |c k| ≤ K)
    (Y : RealMatrix n n) : frobeniusNormSq (cw c Y) ≤ K ^ 2 * frobeniusNormSq Y := by
  unfold frobeniusNormSq cw
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun j _ => ?_)
  have h := hc ((eqv n).symm (i, j))
  have h2 : c ((eqv n).symm (i, j)) ^ 2 ≤ K ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_right h2 (sq_nonneg _)

lemma Bop_bound {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (c : Fin (n * n) → ℝ) (K : ℝ)
    (hc : ∀ k, |c k| ≤ K) (v : Fin (n * n) → ℝ) :
    ∑ m, (Matrix.mulVec (Bop SV c) v m) ^ 2 ≤ K ^ 2 * ∑ m, v m ^ 2 := by
  rw [← vecR_unvec v, Bop_vec, sumsq_vecR, sumsq_vecR]
  calc _ ≤ frobeniusNormSq (cw c (tangentProjection SV (unvec v))) := frobSq_T_le SV _
    _ ≤ K ^ 2 * frobeniusNormSq (tangentProjection SV (unvec v)) := frobSq_cw_le c K hc _
    _ ≤ K ^ 2 * frobeniusNormSq (unvec v) :=
        mul_le_mul_of_nonneg_left (frobSq_T_le SV _) (sq_nonneg _)

lemma rank1_bound {N : ℕ} (a v : Fin N → ℝ) (t : ℝ) :
    ∑ m, (Matrix.mulVec (t • Matrix.vecMulVec a a) v m) ^ 2 ≤
      (t * ∑ m, a m ^ 2) ^ 2 * ∑ m, v m ^ 2 := by
  have e : ∀ m, Matrix.mulVec (t • Matrix.vecMulVec a a) v m = t * a m * ∑ m', a m' * v m' := by
    intro m
    simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul,
      Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  simp_rw [e]
  have e2 : ∀ m, (t * a m * ∑ m', a m' * v m') ^ 2 = t ^ 2 * (∑ m', a m' * v m') ^ 2 * a m ^ 2 := by
    intro m; ring
  simp_rw [e2]
  rw [← Finset.mul_sum]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a v
  have h0 : 0 ≤ ∑ m, a m ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have ht : 0 ≤ t ^ 2 := sq_nonneg t
  calc t ^ 2 * (∑ m', a m' * v m') ^ 2 * ∑ m, a m ^ 2
      ≤ t ^ 2 * ((∑ m, a m ^ 2) * ∑ m, v m ^ 2) * ∑ m, a m ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcs ht) h0
    _ = _ := by ring

/-! ## Real matrices inside complex matrices with the `L²` operator norm -/

def cmap {N : ℕ} (B : Matrix (Fin N) (Fin N) ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  B.map (fun t : ℝ => (t : ℂ))

lemma cmulVec_re {N : ℕ} (B : Matrix (Fin N) (Fin N) ℝ) (x : Fin N → ℂ) (i : Fin N) :
    (Matrix.mulVec (cmap B) x i).re = Matrix.mulVec B (fun j => (x j).re) i := by
  simp only [cmap, Matrix.mulVec, dotProduct, Matrix.map_apply, Complex.re_sum,
    Complex.re_ofReal_mul]

lemma cmulVec_im {N : ℕ} (B : Matrix (Fin N) (Fin N) ℝ) (x : Fin N → ℂ) (i : Fin N) :
    (Matrix.mulVec (cmap B) x i).im = Matrix.mulVec B (fun j => (x j).im) i := by
  simp only [cmap, Matrix.mulVec, dotProduct, Matrix.map_apply, Complex.im_sum,
    Complex.im_ofReal_mul]

section CBridge
open scoped Matrix.Norms.L2Operator

lemma cnorm_le {N : ℕ} (B : Matrix (Fin N) (Fin N) ℝ) (K : ℝ) (hK : 0 ≤ K)
    (h : ∀ v : Fin N → ℝ, ∑ m, (Matrix.mulVec B v m) ^ 2 ≤ K ^ 2 * ∑ m, v m ^ 2) :
    ‖cmap B‖ ≤ K := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hK (fun x => ?_)
  change ‖(WithLp.toLp 2 (Matrix.mulVec (cmap B) (WithLp.ofLp x)) : EuclideanSpace ℂ (Fin N))‖
    ≤ K * ‖x‖
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, ← Real.sqrt_sq hK,
    ← Real.sqrt_mul (sq_nonneg K)]
  apply Real.sqrt_le_sqrt
  have hn : ∀ z : ℂ, ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := fun z => by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hx : ∀ i, x i = WithLp.ofLp x i := fun i => rfl
  simp only [hn, PiLp.toLp_apply, cmulVec_re, cmulVec_im, Finset.sum_add_distrib, hx]
  have h1 := h (fun j => (WithLp.ofLp x j).re)
  have h2 := h (fun j => (WithLp.ofLp x j).im)
  rw [mul_add]
  exact add_le_add h1 h2

lemma real_le_cnorm {N : ℕ} (B : Matrix (Fin N) (Fin N) ℝ) (v : Fin N → ℝ) :
    ∑ m, (Matrix.mulVec B v m) ^ 2 ≤ ‖cmap B‖ ^ 2 * ∑ m, v m ^ 2 := by
  have h := ((Matrix.toEuclideanLin (𝕜 := ℂ) (m := Fin N) (n := Fin N)).trans
    LinearMap.toContinuousLinearMap (cmap B)).le_opNorm (WithLp.toLp 2 (fun j => (v j : ℂ)))
  rw [← Matrix.l2_opNorm_def] at h
  change ‖(WithLp.toLp 2 (Matrix.mulVec (cmap B) (fun j => (v j : ℂ))) :
      EuclideanSpace ℂ (Fin N))‖ ≤
    ‖cmap B‖ * ‖(WithLp.toLp 2 (fun j => (v j : ℂ)) : EuclideanSpace ℂ (Fin N))‖ at h
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq] at h
  have e1 : ∀ i, Matrix.mulVec (cmap B) (fun j => (v j : ℂ)) i =
      ((Matrix.mulVec B v i : ℝ) : ℂ) := by
    intro i
    simp only [cmap, Matrix.mulVec, dotProduct, Matrix.map_apply, Complex.ofReal_sum,
      Complex.ofReal_mul]
  simp only [PiLp.toLp_apply, e1, Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
  have h0 : 0 ≤ ∑ m, (Matrix.mulVec B v m) ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have h0' : 0 ≤ ∑ m, v m ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have h2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
  rw [mul_pow, Real.sq_sqrt h0, Real.sq_sqrt h0'] at h2
  exact h2

end CBridge


/-! ## Part B: the Bernoulli product space -/

open MeasureTheory ProbabilityTheory

noncomputable def bern (ρ : ℝ) : Measure Bool :=
  ENNReal.ofReal ρ • Measure.dirac true + ENNReal.ofReal (1 - ρ) • Measure.dirac false

lemma bern_prob (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) : IsProbabilityMeasure (bern ρ) := by
  constructor
  simp only [bern, Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add h0 (by linarith)]
  simp

lemma bern_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (g : Bool → E) :
    ∫ b, g b ∂(bern ρ) = ρ • g true + (1 - ρ) • g false := by
  unfold bern
  rw [integral_add_measure (Integrable.of_finite.smul_measure ENNReal.ofReal_ne_top)
      (Integrable.of_finite.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure,
    integral_smul_measure, integral_dirac, integral_dirac, ENNReal.toReal_ofReal h0,
    ENNReal.toReal_ofReal (by linarith)]

lemma pi_integral_eval {N : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (k : Fin N) (g : Bool → E) :
    ∫ ω, g (ω k) ∂(Measure.pi (fun _ : Fin N => bern ρ)) = ρ • g true + (1 - ρ) • g false := by
  haveI := bern_prob ρ h0 h1
  have hmp := measurePreserving_eval (fun _ : Fin N => bern ρ) k
  have h := integral_map (μ := Measure.pi (fun _ : Fin N => bern ρ)) (φ := Function.eval k)
    (f := g) (measurable_pi_apply k).aemeasurable Integrable.of_finite.aestronglyMeasurable
  rw [hmp.map_eq] at h
  rw [← bern_integral ρ h0 h1 g]
  exact h.symm

lemma pi_singleton {N : ℕ} (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (ω : Fin N → Bool) :
    (Measure.pi (fun _ : Fin N => bern ρ) {ω}).toReal = ∏ k, (if ω k then ρ else 1 - ρ) := by
  haveI := bern_prob ρ h0 h1
  rw [← Set.univ_pi_singleton ω, Measure.pi_pi, ENNReal.toReal_prod]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  rcases Bool.eq_false_or_eq_true (ω k) with h | h <;>
    simp [h, bern, Measure.dirac_apply, ENNReal.toReal_ofReal h0,
      ENNReal.toReal_ofReal (sub_nonneg.mpr h1)]

lemma pi_toReal_eq_sum {N : ℕ} (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (S : Set (Fin N → Bool)) :
    (Measure.pi (fun _ : Fin N => bern ρ) S).toReal =
      ∑ ω, if ω ∈ S then ∏ k, (if ω k then ρ else 1 - ρ) else 0 := by
  haveI := bern_prob ρ h0 h1
  have hS : S = ↑(Finset.univ.filter (· ∈ S)) := by ext; simp
  conv_lhs => rw [hS]
  rw [← sum_measure_singleton, ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _),
    Finset.sum_filter]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  split_ifs
  · exact pi_singleton ρ h0 h1 ω
  · rfl

def setOf' {n : ℕ} (ω : Fin (n * n) → Bool) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p => ω ((eqv n).symm p) = true)

def boolEquiv (n : ℕ) : (Fin (n * n) → Bool) ≃ Finset (Fin n × Fin n) where
  toFun ω := setOf' ω
  invFun Ω := fun k => decide (eqv n k ∈ Ω)
  left_inv ω := by funext k; simp [setOf']
  right_inv Ω := by ext p; simp [setOf']

lemma bep_eq_sum {n : ℕ} (ρ : ℝ) (F : Finset (Fin n × Fin n) → Prop) :
    bernoulliEventProb ρ F = ∑ ω : Fin (n * n) → Bool,
      if F (setOf' ω) then ∏ k, (if ω k then ρ else 1 - ρ) else 0 := by
  unfold bernoulliEventProb
  refine (Fintype.sum_equiv (boolEquiv n) _ _ (fun ω => ?_)).symm
  change _ = if F (setOf' ω) then bernoulliObservationWeight ρ (setOf' ω) else 0
  split_ifs
  · rw [bw_eq_prod, ← Equiv.prod_comp (eqv n)]
    refine Finset.prod_congr rfl (fun k _ => ?_)
    simp [setOf']
  · rfl

/-! ## Part C: the summands -/

noncomputable def vv {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (k : Fin (n * n)) :
    Matrix (Fin (n * n)) (Fin (n * n)) ℝ :=
  Matrix.vecMulVec (avec SV k) (avec SV k)

noncomputable def tco (ρ : ℝ) (b : Bool) : ℝ := if b then ρ⁻¹ else 0

noncomputable def Sk {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (ρ : ℝ)
    (k : Fin (n * n)) (ω : Fin (n * n) → Bool) : Matrix (Fin (n * n)) (Fin (n * n)) ℂ :=
  cmap (tco ρ (ω k) • vv SV k)

lemma cmap_apply {N : ℕ} (B : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) :
    cmap B i j = (B i j : ℂ) := rfl

lemma cmap_smul {N : ℕ} (t : ℝ) (B : Matrix (Fin N) (Fin N) ℝ) :
    t • cmap B = cmap (t • B) := by
  ext i j
  simp [cmap_apply, Matrix.smul_apply, Complex.real_smul]

lemma cmap_add {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℝ) : cmap A + cmap B = cmap (A + B) := by
  ext i j; simp [cmap_apply]

lemma cmap_sub {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℝ) : cmap A - cmap B = cmap (A - B) := by
  ext i j; simp [cmap_apply]

lemma cmap_sum {N : ℕ} (F : Fin N → Matrix (Fin N) (Fin N) ℝ) :
    ∑ k, cmap (F k) = cmap (∑ k, F k) := by
  ext i j; simp [cmap_apply, Matrix.sum_apply]

lemma vv_sq {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (k : Fin (n * n)) (t : ℝ) :
    cmap (t • vv SV k) * (cmap (t • vv SV k)).conjTranspose =
      cmap ((t ^ 2 * ∑ m, avec SV k m ^ 2) • vv SV k) ∧
    (cmap (t • vv SV k)).conjTranspose * cmap (t • vv SV k) =
      cmap ((t ^ 2 * ∑ m, avec SV k m ^ 2) • vv SV k) := by
  constructor <;>
  · ext i j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, cmap_apply, Matrix.smul_apply,
      vv, Matrix.vecMulVec_apply, smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
    push_cast
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    ring

section Main
open scoped Matrix.Norms.L2Operator

variable {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (ρ : ℝ)


lemma Sk_meas (k : Fin (n * n)) : Measurable (Sk SV ρ k) := measurable_of_countable _

lemma Sk_int (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (k : Fin (n * n)) : Integrable (Sk SV ρ k) (Measure.pi (fun _ : Fin (n * n) => bern ρ)) := by
  haveI := bern_prob ρ h0 h1
  exact Integrable.of_finite

lemma Sk_integral (h0 : 0 < ρ) (h1 : ρ ≤ 1) (k : Fin (n * n)) :
    ∫ ω, Sk SV ρ k ω ∂(Measure.pi (fun _ : Fin (n * n) => bern ρ)) = cmap (vv SV k) := by
  have h := pi_integral_eval ρ h0.le h1 k (fun b => cmap (tco ρ b • vv SV k))
  simp only [Sk]
  rw [h, cmap_smul, cmap_smul, cmap_add]
  congr 1
  simp only [tco, if_true, Bool.false_eq_true, if_false, smul_smul, zero_smul, smul_zero,
    add_zero, mul_inv_cancel₀ h0.ne', one_smul]

lemma Sk_indep (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) : iIndepFun (Sk SV ρ) (Measure.pi (fun _ : Fin (n * n) => bern ρ)) := by
  haveI := bern_prob ρ h0 h1
  exact iIndepFun_pi (X := fun k (b : Bool) => cmap (tco ρ b • vv SV k))
    (fun k => (measurable_of_countable _).aemeasurable)

end Main


/-! ## Part D: applying matrix Bernstein (Tropp, Cor. 6.1.2) -/

section Main2
open scoped Matrix.Norms.L2Operator

variable {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (ρ : ℝ)


lemma Sk_dev (h0 : 0 < ρ) (h1 : ρ ≤ 1) (k : Fin (n * n)) (ω : Fin (n * n) → Bool) :
    Sk SV ρ k ω - ∫ η, Sk SV ρ k η ∂(Measure.pi (fun _ : Fin (n * n) => bern ρ)) = cmap ((tco ρ (ω k) - 1) • vv SV k) := by
  rw [Sk_integral SV ρ h0 h1, Sk, cmap_sub, sub_smul, one_smul]

lemma Z_dev (h0 : 0 < ρ) (h1 : ρ ≤ 1) (ω : Fin (n * n) → Bool) :
    (∑ k, Sk SV ρ k ω) - ∫ η, ∑ k, Sk SV ρ k η ∂(Measure.pi (fun _ : Fin (n * n) => bern ρ)) =
      cmap (Bop SV (fun k => tco ρ (ω k) - 1)) := by
  rw [integral_finsetSum _ (fun k _ => Sk_int SV ρ h0.le h1 k)]
  simp only [Sk_integral SV ρ h0 h1]
  simp only [Sk, cmap_sum, cmap_sub]
  congr 1
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [sub_smul, one_smul]
  rfl

lemma Sk_bound (h0 : 0 < ρ) (h1 : ρ ≤ 1) (μ : ℝ) (hinc : Incoherent SV μ) (k : Fin (n * n))
    (ω : Fin (n * n) → Bool) :
    TroppMatrixConcentration.spectralNorm (Sk SV ρ k ω - ∫ η, Sk SV ρ k η ∂(Measure.pi (fun _ : Fin (n * n) => bern ρ))) ≤
      ρ⁻¹ * (2 * μ * r / n) := by
  rw [Sk_dev SV ρ h0 h1]
  unfold TroppMatrixConcentration.spectralNorm
  have hs0 : 0 ≤ ∑ m, avec SV k m ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hs := avec_sq_le SV μ hinc k
  have hi : 1 ≤ ρ⁻¹ := (one_le_inv₀ h0).mpr h1
  have ht : |tco ρ (ω k) - 1| ≤ ρ⁻¹ := by
    unfold tco
    split_ifs <;> rw [abs_le] <;> constructor <;> linarith
  have hK : 0 ≤ ρ⁻¹ * (2 * μ * r / n) := mul_nonneg (inv_nonneg.mpr h0.le) (hs0.trans hs)
  refine cnorm_le _ _ hK (fun v => ?_)
  refine (rank1_bound (avec SV k) v _).trans
    (mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  rw [← sq_abs, abs_mul, abs_of_nonneg hs0]
  exact pow_le_pow_left₀ (mul_nonneg (abs_nonneg _) hs0)
    (mul_le_mul ht hs hs0 (inv_nonneg.mpr h0.le)) 2

lemma dev_sq_integral (h0 : 0 < ρ) (h1 : ρ ≤ 1) (k : Fin (n * n)) :
    (∫ ω, (Sk SV ρ k ω - ∫ η, Sk SV ρ k η ∂(Measure.pi (fun _ : Fin (n * n) => bern ρ))) *
        (Sk SV ρ k ω - ∫ η, Sk SV ρ k η ∂(Measure.pi (fun _ : Fin (n * n) => bern ρ))).conjTranspose ∂(Measure.pi (fun _ : Fin (n * n) => bern ρ))) =
      cmap (((1 - ρ) / ρ * ∑ m, avec SV k m ^ 2) • vv SV k) ∧
    (∫ ω, (Sk SV ρ k ω - ∫ η, Sk SV ρ k η ∂(Measure.pi (fun _ : Fin (n * n) => bern ρ))).conjTranspose *
        (Sk SV ρ k ω - ∫ η, Sk SV ρ k η ∂(Measure.pi (fun _ : Fin (n * n) => bern ρ))) ∂(Measure.pi (fun _ : Fin (n * n) => bern ρ))) =
      cmap (((1 - ρ) / ρ * ∑ m, avec SV k m ^ 2) • vv SV k) := by
  have hg : ∫ ω, cmap (((tco ρ (ω k) - 1) ^ 2 * ∑ m, avec SV k m ^ 2) • vv SV k) ∂(Measure.pi (fun _ : Fin (n * n) => bern ρ)) =
      cmap (((1 - ρ) / ρ * ∑ m, avec SV k m ^ 2) • vv SV k) := by
    rw [pi_integral_eval ρ h0.le h1 k
      (fun b => cmap (((tco ρ b - 1) ^ 2 * ∑ m, avec SV k m ^ 2) • vv SV k))]
    rw [cmap_smul, cmap_smul, cmap_add, smul_smul, smul_smul, ← add_smul]
    congr 2
    simp only [tco, if_true, Bool.false_eq_true, if_false]
    field_simp
    ring
  simp only [Sk_dev SV ρ h0 h1, (vv_sq SV _ _).1, (vv_sq SV _ _).2]
  exact ⟨hg, hg⟩

lemma V_bound (h0 : 0 < ρ) (h1 : ρ ≤ 1) (μ : ℝ) (hinc : Incoherent SV μ)
    (hK : 0 ≤ ρ⁻¹ * (2 * μ * r / n)) :
    TroppMatrixConcentration.spectralNorm (∑ k, ∫ ω, (Sk SV ρ k ω - ∫ η, Sk SV ρ k η ∂(Measure.pi (fun _ : Fin (n * n) => bern ρ))) *
        (Sk SV ρ k ω - ∫ η, Sk SV ρ k η ∂(Measure.pi (fun _ : Fin (n * n) => bern ρ))).conjTranspose ∂(Measure.pi (fun _ : Fin (n * n) => bern ρ))) ≤ ρ⁻¹ * (2 * μ * r / n) ∧
    TroppMatrixConcentration.spectralNorm (∑ k, ∫ ω, (Sk SV ρ k ω - ∫ η, Sk SV ρ k η ∂(Measure.pi (fun _ : Fin (n * n) => bern ρ))).conjTranspose *
        (Sk SV ρ k ω - ∫ η, Sk SV ρ k η ∂(Measure.pi (fun _ : Fin (n * n) => bern ρ))) ∂(Measure.pi (fun _ : Fin (n * n) => bern ρ))) ≤ ρ⁻¹ * (2 * μ * r / n) := by
  have hsum : ∑ k, cmap (((1 - ρ) / ρ * ∑ m, avec SV k m ^ 2) • vv SV k) =
      cmap (Bop SV (fun k => (1 - ρ) / ρ * ∑ m, avec SV k m ^ 2)) := by
    rw [cmap_sum]; rfl
  have hc : ∀ k, |(1 - ρ) / ρ * ∑ m, avec SV k m ^ 2| ≤ ρ⁻¹ * (2 * μ * r / n) := by
    intro k
    have hs0 : 0 ≤ ∑ m, avec SV k m ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hs := avec_sq_le SV μ hinc k
    have ha : 0 ≤ (1 - ρ) / ρ := div_nonneg (by linarith) h0.le
    have hb : (1 - ρ) / ρ ≤ ρ⁻¹ := by
      rw [div_le_iff₀ h0, inv_mul_cancel₀ h0.ne']; linarith
    rw [abs_of_nonneg (mul_nonneg ha hs0)]
    exact mul_le_mul hb hs hs0 (inv_nonneg.mpr h0.le)
  have hB := cnorm_le _ _ hK (Bop_bound SV _ _ hc)
  simp only [(dev_sq_integral SV ρ h0 h1 _).1, (dev_sq_integral SV ρ h0 h1 _).2, hsum]
  exact ⟨hB, hB⟩

lemma good_of_small (h0 : 0 < ρ) (ω : Fin (n * n) → Bool) (ε : ℝ) (hε : 0 ≤ ε)
    (h : ‖cmap (Bop SV (fun k => tco ρ (ω k) - 1))‖ ≤ ε) :
    ∀ X : RealMatrix n n,
      frobeniusNorm (tangentProjection SV X -
        ρ⁻¹ • tangentProjection SV (samplingProjection (setOf' ω) (tangentProjection SV X))) ≤
        ε * frobeniusNorm X := by
  intro X
  have hcw : cw (fun k => tco ρ (ω k) - 1) (tangentProjection SV X) =
      ρ⁻¹ • samplingProjection (setOf' ω) (tangentProjection SV X) - tangentProjection SV X := by
    ext i j
    simp only [cw, tco, samplingProjection, setOf', Matrix.sub_apply, Matrix.smul_apply,
      smul_eq_mul, Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs <;> ring
  have e : tangentProjection SV X -
      ρ⁻¹ • tangentProjection SV (samplingProjection (setOf' ω) (tangentProjection SV X)) =
      -(tangentProjection SV (cw (fun k => tco ρ (ω k) - 1) (tangentProjection SV X))) := by
    rw [hcw, tangent_sub, tangent_smul, tangent_idem]
    abel
  rw [e]
  have hneg : ∀ M : RealMatrix n n, frobeniusNormSq (-M) = frobeniusNormSq M := by
    intro M; unfold frobeniusNormSq; simp [neg_sq]
  have hY : frobeniusNormSq (-(tangentProjection SV
      (cw (fun k => tco ρ (ω k) - 1) (tangentProjection SV X)))) ≤ ε ^ 2 * frobeniusNormSq X := by
    rw [hneg, ← sumsq_vecR, ← Bop_vec, ← sumsq_vecR]
    refine (real_le_cnorm _ _).trans
      (mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
    exact pow_le_pow_left₀ (norm_nonneg _) h 2
  unfold frobeniusNorm
  calc Real.sqrt (frobeniusNormSq (-(tangentProjection SV
        (cw (fun k => tco ρ (ω k) - 1) (tangentProjection SV X)))))
      ≤ Real.sqrt (ε ^ 2 * frobeniusNormSq X) := Real.sqrt_le_sqrt hY
    _ = ε * Real.sqrt (frobeniusNormSq X) := by
        rw [Real.sqrt_mul (sq_nonneg ε), Real.sqrt_sq hε]

lemma tail_main (h0 : 0 < ρ) (h1 : ρ ≤ 1) (hn : 0 < n) (μ : ℝ) (hinc : Incoherent SV μ)
    (ε : ℝ) (hε : 0 < ε) (hspos : 0 < 2 * μ * r / n) :
    bernoulliEventProb ρ (fun Ω => ¬ ∀ X : RealMatrix n n,
        frobeniusNorm (tangentProjection SV X -
          ρ⁻¹ • tangentProjection SV (samplingProjection Ω (tangentProjection SV X))) ≤
          ε * frobeniusNorm X) ≤
      ((n * n + n * n : ℕ) : ℝ) * Real.exp (-(ε ^ 2 / 2) /
        (ρ⁻¹ * (2 * μ * r / n) + ρ⁻¹ * (2 * μ * r / n) * ε / 3)) := by
  haveI := bern_prob ρ h0.le h1
  haveI : NeZero (n * n) := ⟨by positivity⟩
  have hL : 0 ≤ ρ⁻¹ * (2 * μ * r / n) := mul_nonneg (inv_nonneg.mpr h0.le) hspos.le
  have H := IntroMatrixConc.Sampling.corollary_6_1_2 (Measure.pi (fun _ : Fin (n * n) => bern ρ)) (Sk SV ρ) (ρ⁻¹ * (2 * μ * r / n)) hL
    (Sk_meas SV ρ) (Sk_int SV ρ h0.le h1) (Sk_indep SV ρ h0.le h1)
    (fun k => Filter.Eventually.of_forall (fun ω => Sk_bound SV ρ h0 h1 μ hinc k ω))
  dsimp only at H
  obtain ⟨hV, -, htail⟩ := H
  have hT := htail ε hε.le
  have hVb := V_bound SV ρ h0 h1 μ hinc hL
  have hVle : TroppMatrixConcentration.rectSecondMoment (Measure.pi (fun _ : Fin (n * n) => bern ρ))
      (fun ω => ∑ k, Sk SV ρ k ω - ∫ η, ∑ k, Sk SV ρ k η ∂(Measure.pi (fun _ : Fin (n * n) => bern ρ))) ≤ ρ⁻¹ * (2 * μ * r / n) := by
    rw [hV]; exact max_le hVb.1 hVb.2
  have hV0 : 0 ≤ TroppMatrixConcentration.rectSecondMoment (Measure.pi (fun _ : Fin (n * n) => bern ρ))
      (fun ω => ∑ k, Sk SV ρ k ω - ∫ η, ∑ k, Sk SV ρ k η ∂(Measure.pi (fun _ : Fin (n * n) => bern ρ))) := by
    unfold TroppMatrixConcentration.rectSecondMoment TroppMatrixConcentration.spectralNorm
    exact le_max_of_le_left (norm_nonneg _)
  rw [bep_eq_sum]
  have hw : ∀ ω : Fin (n * n) → Bool, 0 ≤ ∏ k, (if ω k then ρ else 1 - ρ) := fun ω =>
    Finset.prod_nonneg (fun k _ => by split_ifs <;> linarith)
  calc _ ≤ ∑ ω : Fin (n * n) → Bool, (if ω ∈ {ω | ε ≤ TroppMatrixConcentration.spectralNorm
          (∑ k, Sk SV ρ k ω - ∫ η, ∑ k, Sk SV ρ k η ∂(Measure.pi (fun _ : Fin (n * n) => bern ρ)))} then
          ∏ k, (if ω k then ρ else 1 - ρ) else 0) := by
        refine Finset.sum_le_sum (fun ω _ => ?_)
        by_cases hg : ∀ X : RealMatrix n n,
            frobeniusNorm (tangentProjection SV X -
              ρ⁻¹ • tangentProjection SV (samplingProjection (setOf' ω) (tangentProjection SV X))) ≤
              ε * frobeniusNorm X
        · rw [if_neg (not_not.mpr hg)]
          split_ifs
          · exact hw ω
          · exact le_rfl
        · rw [if_pos hg, if_pos]
          rw [Set.mem_setOf_eq]
          by_contra hlt
          push Not at hlt
          apply hg
          refine good_of_small SV ρ h0 ω ε hε.le ?_
          rw [← Z_dev SV ρ h0 h1 ω]
          exact hlt.le
    _ = ((Measure.pi (fun _ : Fin (n * n) => bern ρ)) {ω | ε ≤ TroppMatrixConcentration.spectralNorm
          (∑ k, Sk SV ρ k ω - ∫ η, ∑ k, Sk SV ρ k η ∂(Measure.pi (fun _ : Fin (n * n) => bern ρ)))}).toReal :=
        (pi_toReal_eq_sum ρ h0.le h1 _).symm
    _ ≤ _ := hT
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
        rw [neg_div, neg_div, neg_le_neg_iff]
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        linarith

end Main2

lemma arith26 (n : ℕ) (hn : 0 < n) (μ r ρ ε : ℝ) (hμr : 0 < μ * r) (hε : 0 < ε) (hε1 : ε < 1)
    (hρ0 : 0 < ρ) (hρ : ρ ≥ 64 * ε⁻¹ ^ 2 * μ * r * Real.log n / n) :
    ((n * n + n * n : ℕ) : ℝ) * Real.exp (-(ε ^ 2 / 2) /
        (ρ⁻¹ * (2 * μ * r / n) + ρ⁻¹ * (2 * μ * r / n) * ε / 3)) ≤
      2 * (n : ℝ) ^ (-10 : ℤ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hs : 0 < 2 * μ * r / n := div_pos (by linarith) hnR
  have hD : 0 < ρ⁻¹ * (2 * μ * r / n) + ρ⁻¹ * (2 * μ * r / n) * ε / 3 := by positivity
  have hρ' : 64 * (μ * r * Real.log n) ≤ ε ^ 2 * ρ * n := by
    have h2 := hρ
    rw [ge_iff_le, div_le_iff₀ hnR] at h2
    calc 64 * (μ * r * Real.log n) = ε ^ 2 * (64 * ε⁻¹ ^ 2 * μ * r * Real.log n) := by
          field_simp
      _ ≤ ε ^ 2 * (ρ * n) := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
      _ = ε ^ 2 * ρ * n := by ring
  have hkey : 12 * Real.log n ≤ (ε ^ 2 / 2) /
      (ρ⁻¹ * (2 * μ * r / n) + ρ⁻¹ * (2 * μ * r / n) * ε / 3) := by
    rw [le_div_iff₀ hD]
    have e : 12 * Real.log n * (ρ⁻¹ * (2 * μ * r / n) + ρ⁻¹ * (2 * μ * r / n) * ε / 3) =
        (24 * (μ * r * Real.log n) * (1 + ε / 3)) / (ρ * n) := by
      field_simp
      ring
    rw [e, div_le_iff₀ (by positivity)]
    have hq0 : 0 ≤ μ * r * Real.log n := mul_nonneg hμr.le hlog
    have hq1 := mul_nonneg hq0 (by linarith : (0 : ℝ) ≤ 1 - ε)
    nlinarith
  have hexp : Real.exp (-(ε ^ 2 / 2) /
      (ρ⁻¹ * (2 * μ * r / n) + ρ⁻¹ * (2 * μ * r / n) * ε / 3)) ≤
      Real.exp (-((12 : ℕ) * Real.log n)) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div]
    push_cast
    linarith
  have hq : Real.exp (-((12 : ℕ) * Real.log n)) = ((n : ℝ) ^ 12)⁻¹ := by
    rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log hnR]
  have hz : (n : ℝ) ^ (-10 : ℤ) = ((n : ℝ) ^ 10)⁻¹ := by
    simp [zpow_neg]
  rw [hz]
  calc _ ≤ ((n * n + n * n : ℕ) : ℝ) * ((n : ℝ) ^ 12)⁻¹ := by
        rw [← hq]; exact mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = 2 * ((n : ℝ) ^ 10)⁻¹ := by
        push_cast
        field_simp
        ring

theorem main26 : ∃ C0 c : ℝ, 0 < C0 ∧ 0 < c ∧
      ∀ (n r : ℕ) (L0 : RealMatrix n n) (SV : SVD L0 r) (μ ε ρ0 : ℝ),
        0 < n → Incoherent SV μ → 0 < ε → ε < 1 → 0 < ρ0 → ρ0 ≤ 1 →
        ρ0 ≥ C0 * ε⁻¹ ^ 2 * μ * r * Real.log n / n →
        bernoulliEventProb ρ0 (fun Ω => ∀ X : RealMatrix n n,
            frobeniusNorm (tangentProjection SV X -
              ρ0⁻¹ • tangentProjection SV (samplingProjection Ω (tangentProjection SV X))) ≤
              ε * frobeniusNorm X) ≥
          1 - c * (n : ℝ) ^ (-10 : ℤ) := by
  refine ⟨64, 2, by norm_num, by norm_num, ?_⟩
  intro n r L0 SV μ ε ρ0 hn hinc hε0 hε1 hρ0 hρ1 hρ
  have hnot := bep_not (N := n) ρ0 (fun Ω => ∀ X : RealMatrix n n,
      frobeniusNorm (tangentProjection SV X -
        ρ0⁻¹ • tangentProjection SV (samplingProjection Ω (tangentProjection SV X))) ≤
        ε * frobeniusNorm X)
  suffices hs : bernoulliEventProb ρ0 (fun Ω => ¬ ∀ X : RealMatrix n n,
      frobeniusNorm (tangentProjection SV X -
        ρ0⁻¹ • tangentProjection SV (samplingProjection Ω (tangentProjection SV X))) ≤
        ε * frobeniusNorm X) ≤ 2 * (n : ℝ) ^ (-10 : ℤ) by
    rw [ge_iff_le]; linarith
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    have hz : ∀ X : RealMatrix n n, tangentProjection SV X = 0 := by
      intro X; ext i j; simp [tangent_eq, Matrix.mul_apply, PU, PV, projM]
    have h0 : bernoulliEventProb ρ0 (fun Ω => ¬ ∀ X : RealMatrix n n,
        frobeniusNorm (tangentProjection SV X -
          ρ0⁻¹ • tangentProjection SV (samplingProjection Ω (tangentProjection SV X))) ≤
          ε * frobeniusNorm X) = 0 := by
      unfold bernoulliEventProb
      refine Finset.sum_eq_zero (fun Ω _ => if_neg ?_)
      push Not
      intro X
      have hf : frobeniusNorm (0 : RealMatrix n n) = 0 := by
        simp [frobeniusNorm, frobeniusNormSq]
      have hX : 0 ≤ frobeniusNorm X := Real.sqrt_nonneg _
      simp only [hz, smul_zero, sub_zero, hf]
      positivity
    rw [h0]; positivity
  · have hμ := mu_ge_one SV μ hn hr hinc
    have hrR : (0 : ℝ) < r := by exact_mod_cast hr
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hμr : 0 < μ * r := by positivity
    have hspos : 0 < 2 * μ * r / n := div_pos (by linarith) hnR
    exact (tail_main SV ρ0 hρ0 hρ1 hn μ hinc ε hε0 hspos).trans
      (arith26 n hn μ r ρ0 ε hμr hε0 hε1 hρ0 hρ)

end RPCA26

open RPCA26

open RobustPCA.Recovery MatrixCompletion in
theorem solution :
    ∃ C0 c : ℝ, 0 < C0 ∧ 0 < c ∧
      ∀ (n r : ℕ) (L0 : RealMatrix n n) (SV : SVD L0 r) (μ ε ρ0 : ℝ),
        0 < n → Incoherent SV μ → 0 < ε → ε < 1 → 0 < ρ0 → ρ0 ≤ 1 →
        ρ0 ≥ C0 * ε⁻¹ ^ 2 * μ * r * Real.log n / n →
        bernoulliEventProb ρ0 (fun Ω => ∀ X : RealMatrix n n,
            frobeniusNorm (tangentProjection SV X -
              ρ0⁻¹ • tangentProjection SV (samplingProjection Ω (tangentProjection SV X))) ≤
              ε * frobeniusNorm X) ≥
          1 - c * (n : ℝ) ^ (-10 : ℤ) := by
  exact main26
