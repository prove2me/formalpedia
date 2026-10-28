-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P48.complementary_transfer
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-25T18:53:53.010979+00:00
-- url     : https://prove2.me/submissions/b6ee4be2-2a49-412a-b1ac-31d0a03b80db

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P48

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace P48Aux

open scoped Matrix.Norms.L2Operator
open Matrix Polynomial
open scoped ComplexOrder

/-- TR: trace of a Hermitian functional calculus. -/
lemma trace_cfc_herm {n : Type*} [Fintype n] [DecidableEq n] {X : Matrix n n ℂ}
    (hX : X.IsHermitian) (f : ℝ → ℝ) :
    (cfc f X).trace = ∑ j, ((f (hX.eigenvalues j) : ℝ) : ℂ) := by
  rw [hX.cfc_eq, Matrix.IsHermitian.cfc]
  simp only [Unitary.conjStarAlgAut_apply]
  rw [Matrix.trace_mul_cycle]
  have hu : (star (hX.eigenvectorUnitary : Matrix n n ℂ)) * (hX.eigenvectorUnitary : Matrix n n ℂ) = 1 :=
    Unitary.coe_star_mul_self _
  rw [hu, one_mul, Matrix.trace_diagonal]
  rfl

lemma roots_rel {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {X : Matrix m m ℂ} {Y : Matrix n n ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian) {k1 k2 : ℕ}
    (h : (Polynomial.X : ℂ[X]) ^ k1 * X.charpoly = Polynomial.X ^ k2 * Y.charpoly) :
    k1 • ({0} : Multiset ℂ) + Multiset.map (RCLike.ofReal ∘ hX.eigenvalues) Finset.univ.val =
      k2 • ({0} : Multiset ℂ) + Multiset.map (RCLike.ofReal ∘ hY.eigenvalues) Finset.univ.val := by
  have h1 : ((Polynomial.X : ℂ[X]) ^ k1 * X.charpoly) ≠ 0 :=
    ((Polynomial.monic_X_pow k1).mul (Matrix.charpoly_monic X)).ne_zero
  have h2 : ((Polynomial.X : ℂ[X]) ^ k2 * Y.charpoly) ≠ 0 :=
    ((Polynomial.monic_X_pow k2).mul (Matrix.charpoly_monic Y)).ne_zero
  have hr := congrArg Polynomial.roots h
  rw [Polynomial.roots_mul h1, Polynomial.roots_mul h2, Polynomial.roots_X_pow,
    Polynomial.roots_X_pow, hX.roots_charpoly_eq_eigenvalues,
    hY.roots_charpoly_eq_eigenvalues] at hr
  exact hr

/-- S1. -/
lemma trace_cfc_of_charpoly {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {X : Matrix m m ℂ} {Y : Matrix n n ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian) {k1 k2 : ℕ}
    (h : (Polynomial.X : ℂ[X]) ^ k1 * X.charpoly = Polynomial.X ^ k2 * Y.charpoly)
    (f : ℝ → ℝ) (hf : f 0 = 0) : (cfc f X).trace = (cfc f Y).trace := by
  have hr := congrArg (fun s : Multiset ℂ => (s.map (fun z => ((f z.re : ℝ) : ℂ))).sum)
    (roots_rel hX hY h)
  simp only [Multiset.map_add, Multiset.sum_add, Multiset.map_nsmul, Multiset.map_singleton,
    Multiset.sum_nsmul, Multiset.sum_singleton, Complex.zero_re, hf, Complex.ofReal_zero,
    smul_zero, zero_add, Multiset.map_map, Function.comp_def] at hr
  have key : ∀ x : ℝ, (RCLike.ofReal x : ℂ).re = x := fun x => by simp
  simp only [key] at hr
  rw [trace_cfc_herm hX, trace_cfc_herm hY]
  simpa only [Finset.sum_eq_multiset_sum] using hr

lemma norm_unitary_mul {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (U : Matrix m m ℂ) (hU : Uᴴ * U = 1) (A : Matrix m n ℂ) : ‖U * A‖ = ‖A‖ := by
  have h1 : ‖(U * A)ᴴ * (U * A)‖ = ‖Aᴴ * A‖ := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ, hU, Matrix.one_mul]
  rw [Matrix.l2_opNorm_conjTranspose_mul_self, Matrix.l2_opNorm_conjTranspose_mul_self] at h1
  have := norm_nonneg (U * A); have := norm_nonneg A
  nlinarith [sq_nonneg (‖U * A‖ - ‖A‖), sq_nonneg (‖U * A‖ + ‖A‖)]

lemma norm_mul_unitary {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (U : Matrix n n ℂ) (hU : Uᴴ * U = 1) (A : Matrix m n ℂ) : ‖A * Uᴴ‖ = ‖A‖ := by
  rw [← Matrix.l2_opNorm_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    norm_unitary_mul U hU, Matrix.l2_opNorm_conjTranspose]

lemma norm_herm {n : Type*} [Fintype n] [DecidableEq n] {X : Matrix n n ℂ} (hX : X.IsHermitian) :
    ‖X‖ = ((Finset.univ.val.map (fun j => ‖((hX.eigenvalues j : ℝ) : ℂ)‖₊)).sup : NNReal) := by
  have hU : (hX.eigenvectorUnitary : Matrix n n ℂ)ᴴ * (hX.eigenvectorUnitary : Matrix n n ℂ) = 1 :=
    Unitary.coe_star_mul_self _
  conv_lhs => rw [hX.spectral_theorem]
  simp only [Unitary.conjStarAlgAut_apply]
  rw [show star (hX.eigenvectorUnitary : Matrix n n ℂ) = (hX.eigenvectorUnitary : Matrix n n ℂ)ᴴ
    from rfl, norm_mul_unitary _ hU, norm_unitary_mul _ hU, Matrix.l2_opNorm_diagonal, Pi.norm_def]
  rfl

/-- S2. -/
lemma norm_of_charpoly {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {X : Matrix m m ℂ} {Y : Matrix n n ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian) {k1 k2 : ℕ}
    (h : (Polynomial.X : ℂ[X]) ^ k1 * X.charpoly = Polynomial.X ^ k2 * Y.charpoly) :
    ‖X‖ = ‖Y‖ := by
  have hr := congrArg (fun s : Multiset ℂ => (s.map (fun z => ‖z‖₊)).sup) (roots_rel hX hY h)
  have hz : ∀ k : ℕ, ((k • ({0} : Multiset ℂ)).map (fun z => ‖z‖₊)).sup = 0 := by
    intro k
    apply le_antisymm _ (by simp)
    apply Multiset.sup_le.mpr
    intro b hb
    rw [Multiset.map_nsmul, Multiset.map_singleton] at hb
    rcases Multiset.mem_nsmul.mp hb with ⟨_, hb⟩
    rw [Multiset.mem_singleton] at hb
    simp [hb]
  simp only [Multiset.map_add, Multiset.sup_add, hz, Multiset.map_map] at hr
  rw [norm_herm hX, norm_herm hY]
  simpa [Function.comp_def, bot_eq_zero] using hr

section S3
variable {B C : Type*} [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]

lemma charpoly_rel1 (M : Matrix B C ℂ) :
    (Polynomial.X : ℂ[X]) ^ Fintype.card C * (M * Mᴴ).charpoly =
      Polynomial.X ^ Fintype.card B * ((Mᴴ * M)ᵀ).charpoly := by
  rw [Matrix.charpoly_transpose]; exact Matrix.charpoly_mul_comm' M Mᴴ

lemma charpoly_rel2 (M : Matrix B C ℂ) :
    (Polynomial.X : ℂ[X]) ^ Fintype.card C * ((M * Mᴴ)ᴴ * (M * Mᴴ)).charpoly =
      Polynomial.X ^ Fintype.card B * (((Mᴴ * M)ᵀ)ᴴ * (Mᴴ * M)ᵀ).charpoly := by
  have e1 : (M * Mᴴ)ᴴ * (M * Mᴴ) = (M * Mᴴ * M) * Mᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]; simp only [Matrix.mul_assoc]
  have hY : ((Mᴴ * M)ᵀ).IsHermitian := (Matrix.isHermitian_conjTranspose_mul_self M).transpose
  have e2 : ((Mᴴ * M)ᵀ)ᴴ * (Mᴴ * M)ᵀ = (Mᴴ * (M * Mᴴ * M))ᵀ := by
    rw [hY.eq, ← Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
  rw [e1, e2, Matrix.charpoly_transpose]
  exact Matrix.charpoly_mul_comm' (M * Mᴴ * M) Mᴴ

lemma entropy_mm (M : Matrix B C ℂ) :
    QAlgorithms.Papers.Independent.Information100.P56.entropy (M * Mᴴ) =
      QAlgorithms.Papers.Independent.Information100.P56.entropy ((Mᴴ * M)ᵀ) := by
  unfold QAlgorithms.Papers.Independent.Information100.P56.entropy
  rw [trace_cfc_of_charpoly (Matrix.isHermitian_mul_conjTranspose_self M)
    (Matrix.isHermitian_conjTranspose_mul_self M).transpose (charpoly_rel1 M) _ (by simp)]

lemma specNorm_eq_norm {I : Type*} [Fintype I] [DecidableEq I] (X : Matrix I I ℂ) :
    QAlgorithms.specNorm X = ‖X‖ := rfl

lemma schatten_mm (p : ENNReal) (hp : 1 ≤ p) (M : Matrix B C ℂ) :
    QAlgorithms.Papers.Independent.Information100.P50.schattenNorm p (M * Mᴴ) =
      QAlgorithms.Papers.Independent.Information100.P50.schattenNorm p ((Mᴴ * M)ᵀ) := by
  unfold QAlgorithms.Papers.Independent.Information100.P50.schattenNorm
  by_cases ht : p = ⊤
  · simp only [ht, if_true]; rw [specNorm_eq_norm, specNorm_eq_norm]
    exact norm_of_charpoly (Matrix.isHermitian_mul_conjTranspose_self M)
      (Matrix.isHermitian_conjTranspose_mul_self M).transpose (charpoly_rel1 M)
  · simp only [ht, if_false]
    have hp1 : (1 : ℝ) ≤ p.toReal := by
      have := ENNReal.toReal_mono ht hp; simpa using this
    rw [trace_cfc_of_charpoly (Matrix.isHermitian_conjTranspose_mul_self _)
      (Matrix.isHermitian_conjTranspose_mul_self _) (charpoly_rel2 M) _
      (by rw [Real.rpow_eq_pow, Real.zero_rpow (by positivity)])]

end S3

section Dil
open QAlgorithms
open QAlgorithms.Papers.Independent.Information100.P67 (receiverChannel complementaryChannel)
variable {A B C : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]

/-- The reshaped output vector `V ψ` as a `B × C` matrix. -/
def dilVec (V : Matrix (B × C) A ℂ) (ψ : EuclideanSpace ℂ A) : Matrix B C ℂ :=
  Matrix.of fun b c => ∑ a, V (b, c) a * ψ a

lemma recv_pure (V : Matrix (B × C) A ℂ) (ψ : EuclideanSpace ℂ A) :
    receiverChannel V (pureDensity ψ) = dilVec V ψ * (dilVec V ψ)ᴴ := by
  ext b b'
  simp only [receiverChannel, traceRight, pureDensity, dilVec, Matrix.of_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, star_sum, star_mul', Finset.sum_mul, Finset.mul_sum, starRingEnd_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

lemma compl_pure (V : Matrix (B × C) A ℂ) (ψ : EuclideanSpace ℂ A) :
    complementaryChannel V (pureDensity ψ) = ((dilVec V ψ)ᴴ * dilVec V ψ)ᵀ := by
  ext c c'
  simp only [complementaryChannel, traceLeft, pureDensity, dilVec, Matrix.of_apply, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.conjTranspose_apply, star_sum, star_mul', Finset.sum_mul,
    Finset.mul_sum, starRingEnd_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

lemma entropy_pure (V : Matrix (B × C) A ℂ) (ψ : EuclideanSpace ℂ A) :
    QAlgorithms.Papers.Independent.Information100.P56.entropy (receiverChannel V (pureDensity ψ)) =
      QAlgorithms.Papers.Independent.Information100.P56.entropy
        (complementaryChannel V (pureDensity ψ)) := by
  rw [recv_pure, compl_pure, entropy_mm]

lemma schatten_pure (p : ENNReal) (hp : 1 ≤ p) (V : Matrix (B × C) A ℂ) (ψ : EuclideanSpace ℂ A) :
    QAlgorithms.Papers.Independent.Information100.P50.schattenNorm p
        (receiverChannel V (pureDensity ψ)) =
      QAlgorithms.Papers.Independent.Information100.P50.schattenNorm p
        (complementaryChannel V (pureDensity ψ)) := by
  rw [recv_pure, compl_pure, schatten_mm p hp]

/-- SWP: swapping the two output factors exchanges the marginals. -/
def swapDil (V : Matrix (B × C) A ℂ) : Matrix (C × B) A ℂ := Matrix.of fun cb a => V (cb.2, cb.1) a

lemma recv_swap (V : Matrix (B × C) A ℂ) : receiverChannel (swapDil V) = complementaryChannel V := by
  funext ρ; ext c c'
  simp [receiverChannel, complementaryChannel, traceRight, traceLeft, swapDil, Matrix.mul_apply]

lemma compl_swap (V : Matrix (B × C) A ℂ) : complementaryChannel (swapDil V) = receiverChannel V := by
  funext ρ; ext b b'
  simp [receiverChannel, complementaryChannel, traceRight, traceLeft, swapDil, Matrix.mul_apply]

end Dil

section HH
open QAlgorithms
open QAlgorithms.Papers.Independent.Information100.P67 (receiverChannel complementaryChannel)
variable {A B C : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]

/-- HH: the convex-roof entropies of complementary maps coincide (pure costs agree). -/
lemma hhat_recv_compl (V : Matrix (B × C) A ℂ) :
    QAlgorithms.Papers.Independent.Claimed50.P48.hhat (receiverChannel V) =
      QAlgorithms.Papers.Independent.Claimed50.P48.hhat (complementaryChannel V) := by
  funext ρ
  unfold QAlgorithms.Papers.Independent.Claimed50.P48.hhat
  congr 1
  funext ψ
  exact entropy_pure V ψ

variable {A2 B2 C2 : Type*} [Fintype A2] [DecidableEq A2] [Fintype B2] [DecidableEq B2]
  [Fintype C2] [DecidableEq C2]

omit [DecidableEq B] [DecidableEq C] in
lemma recv_single (V : Matrix (B × C) A ℂ) (a a' : A) (b b' : B) :
    receiverChannel V (Matrix.single a a' 1) b b' = ∑ c, V (b, c) a * star (V (b', c) a') := by
  simp only [receiverChannel, traceRight, Matrix.of_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.single_apply, mul_ite, mul_one, mul_zero]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [ite_and, Finset.sum_ite_eq, Finset.mem_univ, if_true, ite_mul, zero_mul,
    Finset.sum_ite_eq', starRingEnd_apply]

lemma recv_tensor (V : Matrix (B × C) A ℂ) (W : Matrix (B2 × C2) A2 ℂ) :
    receiverChannel (QAlgorithms.Papers.Independent.Claimed50.P48.tensorDilation V W) =
      QAlgorithms.Papers.Independent.Claimed50.P48.superopTensor (receiverChannel V)
        (receiverChannel W) := by
  funext X; ext ⟨b, b2⟩ ⟨b', b2'⟩
  rw [QAlgorithms.Papers.Independent.Claimed50.P48.superopTensor]
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply, recv_single, smul_eq_mul]
  simp only [receiverChannel, traceRight, QAlgorithms.Papers.Independent.Claimed50.P48.tensorDilation,
    Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, star_mul', Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => arg 2; ext y; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  simp only [Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

end HH

section Conv
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma normSq_row (Q : Matrix n n ℂ) (hQ : Q * Qᴴ = 1) (j : n) :
    ∑ k, Complex.normSq (Q j k) = 1 := by
  have h := congrFun (congrFun hQ j) j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at h
  have h2 : ∀ k, Q j k * star (Q j k) = ((Complex.normSq (Q j k) : ℝ) : ℂ) := fun k =>
    Complex.mul_conj (Q j k)
  simp only [h2] at h
  exact_mod_cast h

lemma normSq_col (Q : Matrix n n ℂ) (hQ : Qᴴ * Q = 1) (k : n) :
    ∑ j, Complex.normSq (Q j k) = 1 := by
  have h := congrFun (congrFun hQ k) k
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at h
  have h2 : ∀ j, star (Q j k) * Q j k = ((Complex.normSq (Q j k) : ℝ) : ℂ) := fun j => by
    rw [mul_comm]; exact Complex.mul_conj (Q j k)
  simp only [h2] at h
  exact_mod_cast h

/-- DS: doubly-stochastic Jensen. -/
lemma ds_jensen (Q : Matrix n n ℂ) (hQ : Q * Qᴴ = 1) (hQ' : Qᴴ * Q = 1) (lam : n → ℝ)
    (hlam : ∀ k, 0 ≤ lam k) (g : ℝ → ℝ) (hg : ConvexOn ℝ (Set.Ici 0) g) :
    ∑ j, g (∑ k, Complex.normSq (Q j k) * lam k) ≤ ∑ k, g (lam k) := by
  calc ∑ j, g (∑ k, Complex.normSq (Q j k) * lam k)
      ≤ ∑ j, ∑ k, Complex.normSq (Q j k) * g (lam k) := by
        refine Finset.sum_le_sum fun j _ => ?_
        have := hg.map_sum_le (t := Finset.univ) (w := fun k => Complex.normSq (Q j k)) (p := lam)
          (fun k _ => Complex.normSq_nonneg _) (normSq_row Q hQ j) (fun k _ => hlam k)
        simpa only [smul_eq_mul] using this
    _ = ∑ k, g (lam k) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← Finset.sum_mul, normSq_col Q hQ' k, one_mul]

lemma unitary_prod (U W : Matrix n n ℂ) (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1)
    (hW : Wᴴ * W = 1) (hW' : W * Wᴴ = 1) :
    (Uᴴ * W) * (Uᴴ * W)ᴴ = 1 ∧ (Uᴴ * W)ᴴ * (Uᴴ * W) = 1 := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  constructor
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc W, hW', Matrix.one_mul, hU]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc U, hU', Matrix.one_mul, hW]

lemma pinch_eq {Y : Matrix n n ℂ} (hY : Y.IsHermitian) (U : Matrix n n ℂ) (j : n) :
    ((Uᴴ * Y * U) j j).re =
      ∑ k, Complex.normSq ((Uᴴ * (hY.eigenvectorUnitary : Matrix n n ℂ)) j k) * hY.eigenvalues k := by
  set W : Matrix n n ℂ := (hY.eigenvectorUnitary : Matrix n n ℂ) with hWdef
  have hsp : Y = W * Matrix.diagonal (fun k => ((hY.eigenvalues k : ℝ) : ℂ)) * Wᴴ := by
    conv_lhs => rw [hY.spectral_theorem]
    simp only [Unitary.conjStarAlgAut_apply]
    rfl
  have e : Uᴴ * Y * U =
      (Uᴴ * W) * Matrix.diagonal (fun k => ((hY.eigenvalues k : ℝ) : ℂ)) * (Uᴴ * W)ᴴ := by
    rw [congrArg (fun M => Uᴴ * M * U) hsp, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
  have h1 : ∀ z : ℂ, ∀ r : ℝ, (z * (r : ℂ) * star z).re = Complex.normSq z * r := by
    intro z r
    simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
    ring
  rw [e, Matrix.mul_apply, Complex.re_sum]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
  exact Finset.sum_congr rfl fun k _ => h1 _ _

/-- CONV: trace-function Jensen for a convex combination of PSD matrices. -/
lemma conv_trace {ι : Type*} [Fintype ι] (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i) (hμ1 : ∑ i, μ i = 1)
    (Y : ι → Matrix n n ℂ) (hY : ∀ i, (Y i).PosSemidef) {X : Matrix n n ℂ} (hX : X.IsHermitian)
    (hXY : X = ∑ i, ((μ i : ℝ) : ℂ) • Y i) (g : ℝ → ℝ) (hg : ConvexOn ℝ (Set.Ici 0) g) :
    ∑ j, g (hX.eigenvalues j) ≤ ∑ i, μ i * ∑ k, g ((hY i).1.eigenvalues k) := by
  set U : Matrix n n ℂ := (hX.eigenvectorUnitary : Matrix n n ℂ) with hUdef
  have hU : Uᴴ * U = 1 := Unitary.coe_star_mul_self _
  have hU' : U * Uᴴ = 1 := Unitary.coe_mul_star_self _
  have hd : ∀ i j, ((Uᴴ * Y i * U) j j).re =
      ∑ k, Complex.normSq ((Uᴴ * ((hY i).1.eigenvectorUnitary : Matrix n n ℂ)) j k) *
        (hY i).1.eigenvalues k := fun i j => pinch_eq (hY i).1 U j
  have hd0 : ∀ i j, 0 ≤ ((Uᴴ * Y i * U) j j).re := fun i j => by
    rw [hd]
    exact Finset.sum_nonneg fun k _ =>
      mul_nonneg (Complex.normSq_nonneg _) ((hY i).eigenvalues_nonneg k)
  have heig : ∀ j, hX.eigenvalues j = ∑ i, μ i * ((Uᴴ * Y i * U) j j).re := by
    intro j
    have h1 := pinch_eq hX U j
    rw [← hUdef, hU] at h1
    have h2 : ∑ k, Complex.normSq ((1 : Matrix n n ℂ) j k) * hX.eigenvalues k = hX.eigenvalues j := by
      rw [Finset.sum_eq_single j (fun k _ hk => by simp [Matrix.one_apply_ne (Ne.symm hk)])
        (by simp)]
      simp
    rw [← h2, ← h1, hXY, Matrix.mul_sum, Matrix.sum_mul, Matrix.sum_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, Complex.re_ofReal_mul]
  calc ∑ j, g (hX.eigenvalues j) = ∑ j, g (∑ i, μ i * ((Uᴴ * Y i * U) j j).re) := by
        simp only [← heig]
    _ ≤ ∑ j, ∑ i, μ i * g (((Uᴴ * Y i * U) j j).re) := Finset.sum_le_sum fun j _ => by
        simpa only [smul_eq_mul] using hg.map_sum_le (t := Finset.univ) (w := μ)
          (p := fun i => ((Uᴴ * Y i * U) j j).re) (fun i _ => hμ i) hμ1 (fun i _ => hd0 i j)
    _ = ∑ i, μ i * ∑ j, g (((Uᴴ * Y i * U) j j).re) := by
        rw [Finset.sum_comm]; simp only [Finset.mul_sum]
    _ ≤ _ := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (by
        simp only [hd]
        have hW : ((hY i).1.eigenvectorUnitary : Matrix n n ℂ)ᴴ *
            ((hY i).1.eigenvectorUnitary : Matrix n n ℂ) = 1 := Unitary.coe_star_mul_self _
        have hW' : ((hY i).1.eigenvectorUnitary : Matrix n n ℂ) *
            ((hY i).1.eigenvectorUnitary : Matrix n n ℂ)ᴴ = 1 := Unitary.coe_mul_star_self _
        obtain ⟨q1, q2⟩ := unitary_prod U _ hU hU' hW hW'
        exact ds_jensen _ q1 q2 _ ((hY i).eigenvalues_nonneg) g hg) (hμ i)

lemma herm_comb {ι : Type*} [Fintype ι] (μ : ι → ℝ) (Y : ι → Matrix n n ℂ)
    (hY : ∀ i, (Y i).IsHermitian) : (∑ i, ((μ i : ℝ) : ℂ) • Y i).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.conjTranspose_smul, (hY k).eq, Complex.star_def, Complex.conj_ofReal]

lemma density_decomp {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian) :
    ρ = ∑ k, ((hρ.eigenvalues k : ℝ) : ℂ) • QAlgorithms.pureDensity (hρ.eigenvectorBasis k) := by
  conv_lhs => rw [hρ.spectral_theorem]
  simp only [Unitary.conjStarAlgAut_apply]
  ext a b
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.star_apply, Matrix.sum_apply,
    Matrix.smul_apply, QAlgorithms.pureDensity, Matrix.of_apply, smul_eq_mul,
    Matrix.IsHermitian.eigenvectorUnitary_apply, Function.comp_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  change (hρ.eigenvectorBasis k).ofLp a * ((hρ.eigenvalues k : ℝ) : ℂ) *
    star ((hρ.eigenvectorBasis k).ofLp b) = _
  rw [Complex.star_def]; ring

lemma pure_density (ψ : EuclideanSpace ℂ n) (h : ‖ψ‖ = 1) :
    QAlgorithms.IsDensityMatrix (QAlgorithms.pureDensity ψ) := by
  refine ⟨Matrix.posSemidef_vecMulVec_self_star (WithLp.ofLp ψ), ?_⟩
  have h2 : (inner ℂ ψ ψ : ℂ) = 1 := by rw [inner_self_eq_norm_sq_to_K, h]; simp
  rw [← h2, PiLp.inner_apply]
  simp [Matrix.trace, QAlgorithms.pureDensity, mul_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast; rfl

lemma entropy_eq {X : Matrix n n ℂ} (hX : X.IsHermitian) :
    QAlgorithms.Papers.Independent.Information100.P56.entropy X =
      -∑ j, hX.eigenvalues j * Real.log (hX.eigenvalues j) := by
  unfold QAlgorithms.Papers.Independent.Information100.P56.entropy
  rw [trace_cfc_herm hX, Complex.re_sum]
  simp only [Complex.ofReal_re]

lemma schatten_trace {X : Matrix n n ℂ} (hX : X.IsHermitian) (q : ℝ) (hq : 0 < q) :
    (cfc (fun t : ℝ => Real.rpow t q) (Xᴴ * X)).trace.re =
      ∑ j, Real.rpow (hX.eigenvalues j ^ 2) q := by
  have h1 : Xᴴ * X = X ^ 2 := by rw [hX.eq, sq]
  rw [h1, ← cfc_comp_pow (fun t : ℝ => Real.rpow t q) 2 X
    ((Real.continuous_rpow_const hq.le).continuousOn) hX.isSelfAdjoint,
    trace_cfc_herm hX, Complex.re_sum]
  simp only [Complex.ofReal_re]

lemma wavg_le_max {ι : Type*} [Fintype ι] [Nonempty ι] (μ a : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (h1 : ∑ i, μ i = 1) : ∃ k, ∑ i, μ i * a i ≤ a k := by
  obtain ⟨k, -, hk⟩ := Finset.exists_max_image Finset.univ a Finset.univ_nonempty
  refine ⟨k, ?_⟩
  calc ∑ i, μ i * a i ≤ ∑ i, μ i * a k :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hk i (Finset.mem_univ _)) (hμ i)
    _ = a k := by rw [← Finset.sum_mul, h1, one_mul]

lemma eig_density {ρ : Matrix n n ℂ} (hρ : QAlgorithms.IsDensityMatrix ρ) :
    (∀ k, 0 ≤ hρ.1.1.eigenvalues k) ∧ ∑ k, hρ.1.1.eigenvalues k = 1 := by
  refine ⟨hρ.1.eigenvalues_nonneg, ?_⟩
  have h := hρ.2
  rw [hρ.1.1.trace_eq_sum_eigenvalues] at h
  simpa using congrArg Complex.re h

end Conv

section Main
open QAlgorithms
open QAlgorithms.Papers.Independent.Information100.P67 (receiverChannel complementaryChannel)
open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)
open QAlgorithms.Papers.Independent.Information100.P56 (entropy)
variable {A B C : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]

lemma recv_sum {ι : Type*} [Fintype ι] (V : Matrix (B × C) A ℂ) (c : ι → ℂ) (Y : ι → Matrix A A ℂ) :
    receiverChannel V (∑ i, c i • Y i) = ∑ i, c i • receiverChannel V (Y i) := by
  simp only [receiverChannel]
  rw [Matrix.mul_sum, Matrix.sum_mul]
  simp only [Matrix.mul_smul, Matrix.smul_mul]
  ext b b'
  simp only [traceRight, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  exact Finset.sum_comm

lemma recv_psd (V : Matrix (B × C) A ℂ) (ψ : EuclideanSpace ℂ A) :
    (receiverChannel V (pureDensity ψ)).PosSemidef := by
  rw [recv_pure]; exact Matrix.posSemidef_self_mul_conjTranspose _

lemma recv_decomp (V : Matrix (B × C) A ℂ) {ρ : Matrix A A ℂ} (hρ : ρ.IsHermitian) :
    receiverChannel V ρ = ∑ k, ((hρ.eigenvalues k : ℝ) : ℂ) •
      receiverChannel V (pureDensity (hρ.eigenvectorBasis k)) :=
  (congrArg (receiverChannel V) (density_decomp hρ)).trans (recv_sum V _ _)

lemma ent_ge [Nonempty A] (V : Matrix (B × C) A ℂ) {ρ : Matrix A A ℂ} (hρ : IsDensityMatrix ρ) :
    ∃ ψ : EuclideanSpace ℂ A, ‖ψ‖ = 1 ∧
      entropy (receiverChannel V (pureDensity ψ)) ≤ entropy (receiverChannel V ρ) := by
  have hH := hρ.1.1
  obtain ⟨hμ, hμ1⟩ := eig_density hρ
  have hY : ∀ k, (receiverChannel V (pureDensity (hH.eigenvectorBasis k))).PosSemidef :=
    fun k => recv_psd V _
  have hX : (receiverChannel V ρ).IsHermitian := by
    rw [recv_decomp V hH]; exact herm_comb _ _ fun k => (hY k).1
  have hc := conv_trace _ hμ hμ1 _ hY hX (recv_decomp V hH) (fun x => x * Real.log x)
    Real.convexOn_mul_log
  obtain ⟨k, hk⟩ := wavg_le_max _
    (fun i => ∑ j, (hY i).1.eigenvalues j * Real.log ((hY i).1.eigenvalues j)) hμ hμ1
  refine ⟨hH.eigenvectorBasis k, hH.eigenvectorBasis.orthonormal.1 k, ?_⟩
  rw [entropy_eq hX, entropy_eq (hY k).1]
  linarith

lemma sch_le [Nonempty A] (V : Matrix (B × C) A ℂ) (p : ENNReal) (hp : 1 ≤ p) {ρ : Matrix A A ℂ}
    (hρ : IsDensityMatrix ρ) :
    ∃ ψ : EuclideanSpace ℂ A, ‖ψ‖ = 1 ∧
      schattenNorm p (receiverChannel V ρ) ≤ schattenNorm p (receiverChannel V (pureDensity ψ)) := by
  have hH := hρ.1.1
  obtain ⟨hμ, hμ1⟩ := eig_density hρ
  have hY : ∀ k, (receiverChannel V (pureDensity (hH.eigenvectorBasis k))).PosSemidef :=
    fun k => recv_psd V _
  have hX : (receiverChannel V ρ).IsHermitian := by
    rw [recv_decomp V hH]; exact herm_comb _ _ fun k => (hY k).1
  unfold schattenNorm
  by_cases ht : p = ⊤
  · simp only [ht, if_true, specNorm_eq_norm]
    obtain ⟨k, hk⟩ := wavg_le_max _
      (fun i => ‖receiverChannel V (pureDensity (hH.eigenvectorBasis i))‖) hμ hμ1
    refine ⟨hH.eigenvectorBasis k, hH.eigenvectorBasis.orthonormal.1 k, ?_⟩
    calc ‖receiverChannel V ρ‖ = ‖∑ i, ((hH.eigenvalues i : ℝ) : ℂ) •
          receiverChannel V (pureDensity (hH.eigenvectorBasis i))‖ := by rw [← recv_decomp V hH]
      _ ≤ ∑ i, ‖((hH.eigenvalues i : ℝ) : ℂ) •
          receiverChannel V (pureDensity (hH.eigenvectorBasis i))‖ := norm_sum_le _ _
      _ = ∑ i, hH.eigenvalues i * ‖receiverChannel V (pureDensity (hH.eigenvectorBasis i))‖ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (hμ i)]
      _ ≤ _ := hk
  · simp only [ht, if_false]
    have hp1 : (1 : ℝ) ≤ p.toReal := by
      have := ENNReal.toReal_mono ht hp; simpa using this
    have hq : 0 < p.toReal / 2 := by positivity
    have hg : ConvexOn ℝ (Set.Ici 0) (fun t : ℝ => Real.rpow (t ^ 2) (p.toReal / 2)) := by
      refine (convexOn_rpow hp1).congr fun t ht => ?_
      show t ^ p.toReal = (t ^ 2) ^ (p.toReal / 2)
      rw [← Real.rpow_natCast t 2, ← Real.rpow_mul (Set.mem_Ici.mp ht)]
      congr 1; push_cast; ring
    have hc := conv_trace _ hμ hμ1 _ hY hX (recv_decomp V hH) _ hg
    obtain ⟨k, hk⟩ := wavg_le_max _
      (fun i => ∑ j, Real.rpow ((hY i).1.eigenvalues j ^ 2) (p.toReal / 2)) hμ hμ1
    refine ⟨hH.eigenvectorBasis k, hH.eigenvectorBasis.orthonormal.1 k, ?_⟩
    rw [schatten_trace hX _ hq, schatten_trace (hY k).1 _ hq]
    exact Real.rpow_le_rpow (Finset.sum_nonneg fun j _ => Real.rpow_nonneg (sq_nonneg _) _)
      (hc.trans hk) (by positivity)

end Main

section Fin2
open QAlgorithms
open QAlgorithms.Papers.Independent.Information100.P67 (receiverChannel complementaryChannel)
open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)
open QAlgorithms.Papers.Independent.Information100.P56 (entropy)
open QAlgorithms.Papers.Independent.Claimed50.P48 (nu hmin hhat superopTensor tensorDilation
  SuperadditiveAt indexedKrausDilation rowKraus)
variable {A B C : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]

lemma sSup_congr_ub {s t : Set ℝ} (hs : s.Nonempty) (ht : t.Nonempty)
    (h : upperBounds s = upperBounds t) : sSup s = sSup t := by
  by_cases hb : BddAbove s
  · have h1 := isLUB_csSup hs hb
    have h2 : IsLUB t (sSup s) := by unfold IsLUB; rw [← h]; exact h1
    exact (h2.csSup_eq ht).symm
  · have hb' : ¬ BddAbove t := by unfold BddAbove; rw [← h]; exact hb
    rw [Real.sSup_of_not_bddAbove hb, Real.sSup_of_not_bddAbove hb']

lemma sInf_congr_lb {s t : Set ℝ} (hs : s.Nonempty) (ht : t.Nonempty)
    (h : lowerBounds s = lowerBounds t) : sInf s = sInf t := by
  by_cases hb : BddBelow s
  · have h1 := isGLB_csInf hs hb
    have h2 : IsGLB t (sInf s) := by unfold IsGLB; rw [← h]; exact h1
    exact (h2.csInf_eq ht).symm
  · have hb' : ¬ BddBelow t := by unfold BddBelow; rw [← h]; exact hb
    rw [Real.sInf_of_not_bddBelow hb, Real.sInf_of_not_bddBelow hb']

lemma exists_density [Nonempty A] : ∃ ρ : Matrix A A ℂ, IsDensityMatrix ρ := by
  obtain ⟨a⟩ := ‹Nonempty A›
  exact ⟨_, pure_density (EuclideanSpace.single a (1 : ℂ)) (by simp)⟩

lemma nu_eq [Nonempty A] (V : Matrix (B × C) A ℂ) (p : ENNReal) (hp : 1 ≤ p) :
    nu p (receiverChannel V) = nu p (complementaryChannel V) := by
  unfold nu
  obtain ⟨ρ0, hρ0⟩ := exists_density (A := A)
  refine sSup_congr_ub ⟨_, ρ0, hρ0, rfl⟩ ⟨_, ρ0, hρ0, rfl⟩ ?_
  ext u
  constructor
  · intro hu x hx
    obtain ⟨ρ, hρ, rfl⟩ := hx
    obtain ⟨ψ, hψ, hle⟩ := sch_le (swapDil V) p hp hρ
    rw [recv_swap, ← schatten_pure p hp V ψ] at hle
    exact hle.trans (hu ⟨_, pure_density ψ hψ, rfl⟩)
  · intro hu x hx
    obtain ⟨ρ, hρ, rfl⟩ := hx
    obtain ⟨ψ, hψ, hle⟩ := sch_le V p hp hρ
    rw [schatten_pure p hp V ψ] at hle
    exact hle.trans (hu ⟨_, pure_density ψ hψ, rfl⟩)

lemma hmin_eq [Nonempty A] (V : Matrix (B × C) A ℂ) :
    hmin (receiverChannel V) = hmin (complementaryChannel V) := by
  unfold hmin
  obtain ⟨ρ0, hρ0⟩ := exists_density (A := A)
  refine sInf_congr_lb ⟨_, ρ0, hρ0, rfl⟩ ⟨_, ρ0, hρ0, rfl⟩ ?_
  ext u
  constructor
  · intro hu x hx
    obtain ⟨ρ, hρ, rfl⟩ := hx
    obtain ⟨ψ, hψ, hle⟩ := ent_ge (swapDil V) hρ
    rw [recv_swap, ← entropy_pure V ψ] at hle
    exact (hu ⟨_, pure_density ψ hψ, rfl⟩).trans hle
  · intro hu x hx
    obtain ⟨ρ, hρ, rfl⟩ := hx
    obtain ⟨ψ, hψ, hle⟩ := ent_ge V hρ
    rw [entropy_pure V ψ] at hle
    exact (hu ⟨_, pure_density ψ hψ, rfl⟩).trans hle

variable {A2 B2 C2 : Type*} [Fintype A2] [DecidableEq A2] [Fintype B2] [DecidableEq B2]
  [Fintype C2] [DecidableEq C2]

lemma swap_tensor (V : Matrix (B × C) A ℂ) (W : Matrix (B2 × C2) A2 ℂ) :
    swapDil (tensorDilation V W) = tensorDilation (swapDil V) (swapDil W) := by
  ext x a; rfl

lemma compl_tensor (V : Matrix (B × C) A ℂ) (W : Matrix (B2 × C2) A2 ℂ) :
    complementaryChannel (tensorDilation V W) =
      superopTensor (complementaryChannel V) (complementaryChannel W) := by
  rw [← recv_swap, swap_tensor, recv_tensor, recv_swap, recv_swap]

lemma mult_transfer [Nonempty A] [Nonempty A2] (V : Matrix (B × C) A ℂ) (W : Matrix (B2 × C2) A2 ℂ)
    (p : ENNReal) (hp : 1 ≤ p) (h : QAlgorithms.Papers.Independent.Claimed50.P48.Multiplicative p (receiverChannel V)
      (receiverChannel W)) :
    QAlgorithms.Papers.Independent.Claimed50.P48.Multiplicative p (complementaryChannel V) (complementaryChannel W) := by
  unfold QAlgorithms.Papers.Independent.Claimed50.P48.Multiplicative at *
  rw [← compl_tensor, ← nu_eq _ p hp, recv_tensor, h, nu_eq V p hp, nu_eq W p hp]

lemma add_transfer [Nonempty A] [Nonempty A2] (V : Matrix (B × C) A ℂ) (W : Matrix (B2 × C2) A2 ℂ)
    (h : QAlgorithms.Papers.Independent.Claimed50.P48.Additive (receiverChannel V) (receiverChannel W)) :
    QAlgorithms.Papers.Independent.Claimed50.P48.Additive (complementaryChannel V) (complementaryChannel W) := by
  unfold QAlgorithms.Papers.Independent.Claimed50.P48.Additive at *
  rw [← compl_tensor, ← hmin_eq, recv_tensor, h, hmin_eq V, hmin_eq W]

lemma sat_transfer (V : Matrix (B × C) A ℂ) (W : Matrix (B2 × C2) A2 ℂ)
    (ρ : Matrix (A × A2) (A × A2) ℂ) (h : SuperadditiveAt (receiverChannel V) (receiverChannel W) ρ) :
    SuperadditiveAt (complementaryChannel V) (complementaryChannel W) ρ := by
  unfold SuperadditiveAt at *
  rw [← compl_tensor, ← hhat_recv_compl V, ← hhat_recv_compl W, ← hhat_recv_compl, recv_tensor]
  exact h

variable {K : Type*} [Fintype K] [DecidableEq K]

lemma recv_ikd (E : K → Matrix B A ℂ) :
    receiverChannel (indexedKrausDilation E) = krausApply E := by
  funext ρ; ext b b'
  simp [receiverChannel, traceRight, krausApply, indexedKrausDilation, Matrix.mul_apply,
    Matrix.sum_apply]

lemma compl_ikd (E : K → Matrix B A ℂ) :
    complementaryChannel (indexedKrausDilation E) = krausApply (rowKraus E) := by
  funext ρ; ext k k'
  simp [complementaryChannel, traceLeft, krausApply, indexedKrausDilation, rowKraus,
    Matrix.mul_apply, Matrix.sum_apply]

lemma kraus_family (E : K → Matrix B A ℂ) (h : IsKrausFamily E) : IsKrausFamily (rowKraus E) := by
  unfold IsKrausFamily at *
  rw [← h]; ext a a'
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, rowKraus]
  exact Finset.sum_comm

end Fin2

end P48Aux

universe u_1 u_2 u_3 u_5 u_6 u_7

open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P48 QAlgorithms.Papers.Independent.Information100.P67 ENNReal ComplexOrder in
theorem solution {A : Type u_1} {B : Type u_2} {C : Type u_3} {A2 : Type u_5} {B2 : Type u_6}
    {C2 : Type u_7} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] [Fintype A2] [DecidableEq A2] [Fintype B2] [DecidableEq B2]
    [Fintype C2] [DecidableEq C2] [Nonempty A] [Nonempty A2]
    (Phi : Superop A B) (PhiC : Superop A C) (Psi : Superop A2 B2) (PsiC : Superop A2 C2)
    (hPhi : CPComplementary Phi PhiC) (hPsi : CPComplementary Psi PsiC)
    (p : ℝ≥0∞) (hp : ValidExponent p) :
    (Multiplicative p Phi Psi → Multiplicative p PhiC PsiC) ∧
    (IsChannel Phi → IsChannel Psi →
      (Additive Phi Psi → Additive PhiC PsiC) ∧
      (∀ rho, IsDensityMatrix rho → SuperadditiveAt Phi Psi rho → SuperadditiveAt PhiC PsiC rho) ∧
      (Superadditive Phi Psi → Superadditive PhiC PsiC)) ∧
    (UniversalMultiplicative p Phi → UniversalMultiplicative p PhiC) ∧
    (IsChannel Phi → (UniversalAdditive Phi → UniversalAdditive PhiC) ∧
      (UniversalSuperadditive Phi → UniversalSuperadditive PhiC)) := by
  obtain ⟨V, rfl, rfl⟩ := hPhi
  obtain ⟨W, rfl, rfl⟩ := hPsi
  have hp' : 1 ≤ p := hp
  refine ⟨P48Aux.mult_transfer V W p hp', fun _ _ => ⟨P48Aux.add_transfer V W,
    fun ρ _ h => P48Aux.sat_transfer V W ρ h,
    fun h ρ hρ => P48Aux.sat_transfer V W ρ (h ρ hρ)⟩, ?_, fun _ => ⟨?_, ?_⟩⟩
  · intro hU n m hn Ψ hΨ
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    obtain ⟨r, E, rfl⟩ := hΨ
    have h1 := hU n r hn (receiverChannel (P48Aux.swapDil (indexedKrausDilation E)))
      ⟨m, rowKraus E, by rw [P48Aux.recv_swap, P48Aux.compl_ikd]⟩
    have h2 := P48Aux.mult_transfer V _ p hp' h1
    rwa [P48Aux.compl_swap, P48Aux.recv_ikd] at h2
  · intro hU n m hn Ψ hΨ
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    obtain ⟨r, E, hE, hΨE⟩ := hΨ
    obtain rfl : Ψ = krausApply E := funext hΨE
    have h1 := hU n r hn (receiverChannel (P48Aux.swapDil (indexedKrausDilation E)))
      ⟨m, rowKraus E, P48Aux.kraus_family E hE, fun ρ => by rw [P48Aux.recv_swap, P48Aux.compl_ikd]⟩
    have h2 := P48Aux.add_transfer V _ h1
    rwa [P48Aux.compl_swap, P48Aux.recv_ikd] at h2
  · intro hU n m hn Ψ hΨ
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    obtain ⟨r, E, hE, hΨE⟩ := hΨ
    obtain rfl : Ψ = krausApply E := funext hΨE
    have h1 := hU n r hn (receiverChannel (P48Aux.swapDil (indexedKrausDilation E)))
      ⟨m, rowKraus E, P48Aux.kraus_family E hE, fun ρ => by rw [P48Aux.recv_swap, P48Aux.compl_ikd]⟩
    have h2 : Superadditive (complementaryChannel V)
        (complementaryChannel (P48Aux.swapDil (indexedKrausDilation E))) :=
      fun ρ hρ => P48Aux.sat_transfer V _ ρ (h1 ρ hρ)
    rwa [P48Aux.compl_swap, P48Aux.recv_ikd] at h2
