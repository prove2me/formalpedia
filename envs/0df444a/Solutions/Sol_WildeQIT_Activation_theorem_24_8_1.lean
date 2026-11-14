-- Prove2me | solution 1 for WildeQIT.Activation.theorem_24_8_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-13T13:07:33.654015+00:00
-- url     : https://prove2.me/submissions/5ebf6a93-feab-4749-8510-f2ae6ffe0c3a

import Mathlib
import Definitions.Def_WildeQIT_Activation_omegaState
import Definitions.Def_WildeQIT_Activation_IsHalfErasure
import Definitions.Def_WildeQIT_Activation_privateInfoEnsemble
import Definitions.Def_WildeQIT_Activation_coherentInfoChannel
import Definitions.Def_WildeQIT_Degradable_tensorChannel
import Definitions.Def_WildeQIT_Activation_privateInfoChannel

set_option autoImplicit false

open Matrix
open scoped ComplexOrder Kronecker

namespace C2Aux
open WildeQIT

lemma trace_cfc_herm {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).trace = ∑ i, ((f (hA.eigenvalues i) : ℝ) : ℂ) := by
  rw [hA.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_comm,
    ← Matrix.mul_assoc]
  first
    | rw [Unitary.coe_star_mul_self]
    | rw [Unitary.star_mul_self]
    | rw [Matrix.mem_unitaryGroup_iff'.mp hA.eigenvectorUnitary.2]
  rw [Matrix.one_mul, Matrix.trace_diagonal]
  rfl

lemma vn_eq {n : Type*} [Fintype n] [DecidableEq n] {s : Matrix n n ℂ} (hs : s.IsHermitian) :
    QAlgorithms.vnEntropy s = (∑ i, Real.negMulLog (hs.eigenvalues i)) / Real.log 2 := by
  rw [QAlgorithms.vnEntropy, trace_cfc_herm hs, Complex.re_sum, Finset.sum_div, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Complex.ofReal_re, Real.negMulLog, Real.logb]
  ring

lemma trace_eig {n : Type*} [Fintype n] [DecidableEq n] {s : Matrix n n ℂ} (hs : s.IsHermitian) :
    s.trace.re = ∑ i, hs.eigenvalues i := by
  have hsa : IsSelfAdjoint s := hs
  have h1 : cfc (fun x : ℝ => x) s = s := cfc_id' ℝ s hsa
  conv_lhs => rw [← h1]
  rw [trace_cfc_herm hs, Complex.re_sum]
  simp only [Complex.ofReal_re]

/-- spectral decomposition `s = U D Uᴴ` -/
lemma spec {n : Type*} [Fintype n] [DecidableEq n] {s : Matrix n n ℂ} (hs : s.IsHermitian) :
    (hs.eigenvectorUnitary : Matrix n n ℂ) * diagonal (fun i => ((hs.eigenvalues i : ℝ) : ℂ)) *
      star (hs.eigenvectorUnitary : Matrix n n ℂ) = s := by
  have hsa : IsSelfAdjoint s := hs
  have h := cfc_id' ℝ s hsa
  rw [hs.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply] at h
  exact h

lemma unit_mul_star {n : Type*} [Fintype n] [DecidableEq n] {U : Matrix n n ℂ}
    (hU : U ∈ unitaryGroup n ℂ) : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hU

lemma unit_star_mul {n : Type*} [Fintype n] [DecidableEq n] {U : Matrix n n ℂ}
    (hU : U ∈ unitaryGroup n ℂ) : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU

lemma conj_diag {n : Type*} [Fintype n] [DecidableEq n] {s : Matrix n n ℂ} (hs : s.IsHermitian) :
    star (hs.eigenvectorUnitary : Matrix n n ℂ) * s * (hs.eigenvectorUnitary : Matrix n n ℂ) =
      diagonal (fun i => ((hs.eigenvalues i : ℝ) : ℂ)) := by
  have hU := unit_star_mul hs.eigenvectorUnitary.2
  calc _ = star (hs.eigenvectorUnitary : Matrix n n ℂ) * ((hs.eigenvectorUnitary : Matrix n n ℂ) *
        diagonal (fun i => ((hs.eigenvalues i : ℝ) : ℂ)) * star (hs.eigenvectorUnitary : Matrix n n ℂ)) *
        (hs.eigenvectorUnitary : Matrix n n ℂ) := by rw [spec hs]
    _ = _ := by
        simp only [← Matrix.mul_assoc, hU, Matrix.one_mul]
        rw [Matrix.mul_assoc, hU, Matrix.mul_one]

open Polynomial in
lemma sum_eig_of_charpoly {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (d : ι → ℝ)
    (h : A.charpoly = ∏ i, (X - C ((d i : ℝ) : ℂ))) (f : ℝ → ℝ) :
    ∑ i, f (hA.eigenvalues i) = ∑ i, f (d i) := by
  have h1 := hA.roots_charpoly_eq_eigenvalues
  have h2 : A.charpoly.roots = Multiset.map (fun i => ((d i : ℝ) : ℂ)) Finset.univ.val := by
    rw [h, Polynomial.roots_prod]
    · simp
    · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
  have h3 : (A.charpoly.roots.map (fun z => f z.re)).sum = ∑ i, f (hA.eigenvalues i) := by
    rw [h1, Multiset.map_map, Finset.sum_eq_multiset_sum]
    congr 1
  have h4 : (A.charpoly.roots.map (fun z => f z.re)).sum = ∑ i, f (d i) := by
    rw [h2, Multiset.map_map, Finset.sum_eq_multiset_sum]
    congr 1
  rw [← h3, h4]

open Polynomial in
lemma vn_of_charpoly {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (d : ι → ℝ)
    (h : A.charpoly = ∏ i, (X - C ((d i : ℝ) : ℂ))) :
    QAlgorithms.vnEntropy A = (∑ i, Real.negMulLog (d i)) / Real.log 2 := by
  rw [vn_eq hA, sum_eig_of_charpoly hA d h]

lemma vn_charpoly_eq {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {A : Matrix m m ℂ} {B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : A.charpoly = B.charpoly) :
    QAlgorithms.vnEntropy A = QAlgorithms.vnEntropy B := by
  rw [vn_eq hB, vn_of_charpoly hA hB.eigenvalues (h.trans hB.charpoly_eq)]

/-- entropy is invariant under relabelling the basis -/
lemma vn_reindex {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (e : m ≃ n) {A : Matrix m m ℂ} (hA : A.IsHermitian) :
    QAlgorithms.vnEntropy (Matrix.reindex e e A) = QAlgorithms.vnEntropy A := by
  have hB : (Matrix.reindex e e A).IsHermitian := hA.submatrix e.symm
  exact vn_charpoly_eq hB hA (Matrix.charpoly_reindex e A)

/-- entropy is invariant under unitary conjugation -/
lemma vn_unit_conj {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (U : Matrix n n ℂ) (hU : U ∈ unitaryGroup n ℂ) :
    QAlgorithms.vnEntropy (U * A * star U) = QAlgorithms.vnEntropy A := by
  have hB : (U * A * star U).IsHermitian := by
    rw [Matrix.star_eq_conjTranspose]; unfold Matrix.IsHermitian
    simp [Matrix.conjTranspose_mul, hA.eq, Matrix.mul_assoc]
  refine vn_charpoly_eq hB hA ?_
  rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, Matrix.mem_unitaryGroup_iff'.mp hU, Matrix.one_mul]


lemma cq_eq_reindex {X B : Type} [Fintype X] [DecidableEq X] [Fintype B] [DecidableEq B]
    (p : X → ℝ) (σ : X → Matrix B B ℂ) :
    WildeQIT.Degradable.cqState p σ = Matrix.reindex (Equiv.prodComm B X) (Equiv.prodComm B X)
      (blockDiagonal fun x => ((p x : ℂ)) • σ x) := by
  ext ⟨x, i⟩ ⟨y, j⟩
  by_cases h : x = y
  · subst h
    simp [WildeQIT.Degradable.cqState, Matrix.sum_apply, kroneckerMap_apply, Matrix.single_apply,
      blockDiagonal_apply]
  · simp [WildeQIT.Degradable.cqState, Matrix.sum_apply, kroneckerMap_apply, Matrix.single_apply,
      blockDiagonal_apply, h]
    exact Finset.sum_eq_zero fun c _ => by
      rw [if_neg]; rintro ⟨rfl, rfl⟩; exact h rfl

lemma vn_cq {X B : Type} [Fintype X] [DecidableEq X] [Fintype B] [DecidableEq B] (p : X → ℝ)
    (σ : X → Matrix B B ℂ) (hσ : ∀ x, (σ x).IsHermitian) (htr : ∀ x, (σ x).trace = 1) :
    QAlgorithms.vnEntropy (WildeQIT.Degradable.cqState p σ) =
      (∑ x, Real.negMulLog (p x)) / Real.log 2 + ∑ x, p x * QAlgorithms.vnEntropy (σ x) := by
  set U : X → Matrix B B ℂ := fun x => ((hσ x).eigenvectorUnitary : Matrix B B ℂ) with hUdef
  set d : X → B → ℝ := fun x i => p x * (hσ x).eigenvalues i with hd
  have hblk : (blockDiagonal fun x => ((p x : ℂ)) • σ x) =
      blockDiagonal U * blockDiagonal (fun x => diagonal (fun i => ((d x i : ℝ) : ℂ))) *
        star (blockDiagonal U) := by
    rw [star_eq_conjTranspose, blockDiagonal_conjTranspose, ← blockDiagonal_mul, ← blockDiagonal_mul]
    congr 1; funext x
    have hs := spec (hσ x)
    have hD : diagonal (fun i => ((d x i : ℝ) : ℂ)) =
        (p x : ℂ) • diagonal (fun i => (((hσ x).eigenvalues i : ℝ) : ℂ)) := by
      ext i j; by_cases h : i = j <;> simp [diagonal_apply, h, hd]
    rw [hD, Matrix.mul_smul, Matrix.smul_mul]
    simp only [U, star_eq_conjTranspose] at hs ⊢
    rw [hs]
  have hHb : (blockDiagonal fun x => ((p x : ℂ)) • σ x).IsHermitian :=
    isHermitian_blockDiagonal_iff.2 fun x => by
      unfold IsHermitian; rw [conjTranspose_smul, (hσ x).eq]; simp
  have hHD : (blockDiagonal (fun x => diagonal (fun i => ((d x i : ℝ) : ℂ)))).IsHermitian :=
    isHermitian_blockDiagonal_iff.2 fun x => by
      unfold IsHermitian; rw [diagonal_conjTranspose]; congr 1; funext i; simp
  have hW : blockDiagonal U ∈ unitaryGroup (B × X) ℂ := by
    rw [mem_unitaryGroup_iff, star_eq_conjTranspose, blockDiagonal_conjTranspose, ← blockDiagonal_mul]
    rw [← blockDiagonal_one]; congr 1; funext x
    exact unit_mul_star (hσ x).eigenvectorUnitary.2
  rw [cq_eq_reindex, vn_reindex _ hHb, hblk, vn_unit_conj hHD _ hW, blockDiagonal_diagonal]
  rw [vn_of_charpoly (by unfold IsHermitian; rw [diagonal_conjTranspose]; congr 1; funext i; simp) (fun ik : B × X => d ik.2 ik.1)
    (charpoly_diagonal _)]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  have hlog : Real.log 2 ≠ 0 := by positivity
  have hsum : ∀ x, ∑ i, (hσ x).eigenvalues i = 1 := fun x => by
    have h1 := trace_eig (hσ x); rw [htr x] at h1; simpa using h1.symm
  simp only [hd, Real.negMulLog_mul, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hsum]
  rw [Finset.sum_div]
  simp only [vn_eq (hσ _)]
  field_simp
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1
  all_goals exact Finset.sum_congr rfl fun x _ => by field_simp

lemma cq_apply {X B : Type} [Fintype X] [DecidableEq X] [Fintype B] [DecidableEq B]
    (p : X → ℝ) (σ : X → Matrix B B ℂ) (x y : X) (i j : B) :
    WildeQIT.Degradable.cqState p σ (x, i) (y, j) = if x = y then (p x : ℂ) * σ x i j else 0 := by
  rw [cq_eq_reindex]
  simp [reindex_apply, blockDiagonal_apply]

lemma ptr_cq {X B : Type} [Fintype X] [DecidableEq X] [Fintype B] [DecidableEq B]
    (p : X → ℝ) (σ : X → Matrix B B ℂ) (htr : ∀ x, (σ x).trace = 1) :
    partialTraceRight (WildeQIT.Degradable.cqState p σ) = diagonal fun x => (p x : ℂ) := by
  have ht : ∀ x, ∑ k, σ x k k = 1 := fun x => by simpa [Matrix.trace] using htr x
  ext x y
  simp only [partialTraceRight, of_apply, cq_apply]
  by_cases h : x = y
  · subst h; simp [diagonal_apply, ← Finset.mul_sum, ht]
  · simp [diagonal_apply, h]

lemma ptl_cq {X B : Type} [Fintype X] [DecidableEq X] [Fintype B] [DecidableEq B]
    (p : X → ℝ) (σ : X → Matrix B B ℂ) :
    partialTraceLeft (WildeQIT.Degradable.cqState p σ) = ∑ x, p x • σ x := by
  ext k l
  simp [partialTraceLeft, cq_apply, Matrix.sum_apply, Complex.real_smul]

lemma tr_apply {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] (N : QChannel a b)
    (ρ : Matrix a a ℂ) : (N.apply ρ).trace = ρ.trace := by
  unfold QChannel.apply
  rw [Matrix.trace_sum]
  simp_rw [Matrix.trace_mul_cycle _ ρ]
  rw [← Matrix.trace_sum, ← Finset.sum_mul, N.complete, one_mul]

lemma herm_apply {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] (N : QChannel a b)
    {ρ : Matrix a a ℂ} (hρ : ρ.IsHermitian) : (N.apply ρ).IsHermitian := by
  unfold IsHermitian QChannel.apply
  rw [conjTranspose_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [conjTranspose_mul, hρ.eq, Matrix.mul_assoc]

lemma iso_ext {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] (N : QChannel a b) :
    (WildeQIT.Degradable.isometricExtension N)ᴴ * WildeQIT.Degradable.isometricExtension N = 1 := by
  rw [← N.complete]
  ext x x'
  simp only [mul_apply, conjTranspose_apply, WildeQIT.Degradable.isometricExtension, of_apply,
    Matrix.sum_apply, Fintype.sum_prod_type]
  exact Finset.sum_comm

lemma tr_ptl {a b : Type} [Fintype a] [Fintype b] (M : Matrix (a × b) (a × b) ℂ) :
    (partialTraceLeft M).trace = M.trace := by
  simp only [Matrix.trace, diag, partialTraceLeft, of_apply, Fintype.sum_prod_type]
  exact Finset.sum_comm

lemma herm_ptl {a b : Type} [Fintype a] {M : Matrix (a × b) (a × b) ℂ} (hM : M.IsHermitian) :
    (partialTraceLeft M).IsHermitian := by
  ext k l
  simp only [conjTranspose_apply, partialTraceLeft, of_apply, star_sum]
  exact Finset.sum_congr rfl fun i _ => hM.apply _ _

lemma tr_comp {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] (N : QChannel a b)
    (ρ : Matrix a a ℂ) : (WildeQIT.Degradable.complementaryApply N ρ).trace = ρ.trace := by
  unfold WildeQIT.Degradable.complementaryApply
  rw [tr_ptl, Matrix.trace_mul_cycle, iso_ext, one_mul]

lemma herm_comp {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] (N : QChannel a b)
    {ρ : Matrix a a ℂ} (hρ : ρ.IsHermitian) :
    (WildeQIT.Degradable.complementaryApply N ρ).IsHermitian := by
  unfold WildeQIT.Degradable.complementaryApply
  refine herm_ptl ?_
  unfold IsHermitian
  simp [conjTranspose_mul, hρ.eq, Matrix.mul_assoc]

open Classical in
lemma P_eq {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b] (N : QChannel a b)
    (E : WildeQIT.Degradable.CQInput a) :
    WildeQIT.Activation.privateInfoEnsemble N E =
      QAlgorithms.vnEntropy (∑ x, E.p.prob x • N.apply (E.ρ x)) -
        QAlgorithms.vnEntropy (∑ x, E.p.prob x • WildeQIT.Degradable.complementaryApply N (E.ρ x)) -
        ∑ x, E.p.prob x * (QAlgorithms.vnEntropy (N.apply (E.ρ x)) -
          QAlgorithms.vnEntropy (WildeQIT.Degradable.complementaryApply N (E.ρ x))) := by
  have hH : ∀ x, (E.ρ x).IsHermitian := fun x => (E.isDensity x).1.isHermitian
  have ht : ∀ x, (E.ρ x).trace = 1 := fun x => (E.isDensity x).2
  unfold WildeQIT.Activation.privateInfoEnsemble WildeQIT.AFW.qMutualInfo
  rw [ptr_cq _ _ (fun x => (tr_apply N _).trans (ht x)),
    ptr_cq _ _ (fun x => (tr_comp N _).trans (ht x)), ptl_cq, ptl_cq,
    vn_cq _ _ (fun x => herm_apply N (hH x)) (fun x => (tr_apply N _).trans (ht x)),
    vn_cq _ _ (fun x => herm_comp N (hH x)) (fun x => (tr_comp N _).trans (ht x))]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring


end C2Aux

namespace C3Aux
open WildeQIT

lemma trace_cfc_herm {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).trace = ∑ i, ((f (hA.eigenvalues i) : ℝ) : ℂ) := by
  rw [hA.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_comm,
    ← Matrix.mul_assoc]
  first
    | rw [Unitary.coe_star_mul_self]
    | rw [Unitary.star_mul_self]
    | rw [Matrix.mem_unitaryGroup_iff'.mp hA.eigenvectorUnitary.2]
  rw [Matrix.one_mul, Matrix.trace_diagonal]
  rfl

lemma vn_eq {n : Type*} [Fintype n] [DecidableEq n] {s : Matrix n n ℂ} (hs : s.IsHermitian) :
    QAlgorithms.vnEntropy s = (∑ i, Real.negMulLog (hs.eigenvalues i)) / Real.log 2 := by
  rw [QAlgorithms.vnEntropy, trace_cfc_herm hs, Complex.re_sum, Finset.sum_div, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Complex.ofReal_re, Real.negMulLog, Real.logb]
  ring

lemma vn_eq_roots {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    QAlgorithms.vnEntropy A = (A.charpoly.roots.map (fun z => Real.negMulLog z.re)).sum / Real.log 2 := by
  rw [vn_eq hA, hA.roots_charpoly_eq_eigenvalues, Multiset.map_map, Finset.sum_eq_multiset_sum]
  congr 1

/-- `S(AB) = S(BA)` for rectangular `A, B` (nonzero spectra agree, `negMulLog 0 = 0`). -/
lemma vn_mul_comm {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) (B : Matrix n m ℂ) (h1 : (A * B).IsHermitian) (h2 : (B * A).IsHermitian) :
    QAlgorithms.vnEntropy (A * B) = QAlgorithms.vnEntropy (B * A) := by
  have key := congrArg Polynomial.roots (Matrix.charpoly_mul_comm' A B)
  have hne : ∀ (k : ℕ) (p : Polynomial ℂ), p.Monic → (Polynomial.X ^ k * p) ≠ 0 := fun k p hp =>
    mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) hp.ne_zero
  rw [Polynomial.roots_mul (hne _ _ (Matrix.charpoly_monic _)),
    Polynomial.roots_mul (hne _ _ (Matrix.charpoly_monic _)),
    Polynomial.roots_X_pow, Polynomial.roots_X_pow] at key
  have hs : ∀ (k : ℕ) (s : Multiset ℂ), ((k • ({0} : Multiset ℂ) + s).map (fun z => Real.negMulLog z.re)).sum
      = (s.map (fun z => Real.negMulLog z.re)).sum := by
    intro k s
    simp [Multiset.map_add, Multiset.map_nsmul, Multiset.sum_add, Multiset.sum_nsmul]
  rw [vn_eq_roots h1, vn_eq_roots h2, ← hs (Fintype.card n), key, hs]

/-- coefficient matrix of a bipartite vector -/
def coef {X Y : Type*} (ψ : EuclideanSpace ℂ (X × Y)) : Matrix X Y ℂ := Matrix.of fun x y => ψ (x, y)
lemma trace_eig {n : Type*} [Fintype n] [DecidableEq n] {s : Matrix n n ℂ} (hs : s.IsHermitian) :
    s.trace.re = ∑ i, hs.eigenvalues i := by
  have hsa : IsSelfAdjoint s := hs
  have h1 : cfc (fun x : ℝ => x) s = s := cfc_id' ℝ s hsa
  conv_lhs => rw [← h1]
  rw [trace_cfc_herm hs, Complex.re_sum]
  simp only [Complex.ofReal_re]

/-- `S(ρ) ≥ 0` for a density matrix. -/
theorem vn_nonneg {n : Type*} [Fintype n] [DecidableEq n] {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef)
    (htr : ρ.trace = 1) : 0 ≤ QAlgorithms.vnEntropy ρ := by
  have hsum : ∑ i, hρ.1.eigenvalues i = 1 := by rw [← trace_eig hρ.1, htr]; simp
  rw [vn_eq hρ.1]
  refine div_nonneg (Finset.sum_nonneg fun i _ =>
    Real.negMulLog_nonneg (hρ.eigenvalues_nonneg i) ?_) (Real.log_nonneg one_le_two)
  rw [← hsum]
  exact Finset.single_le_sum (fun j _ => hρ.eigenvalues_nonneg j) (Finset.mem_univ i)

/-- `S(ρ) ≤ log₂ d` for a density matrix of dimension `d`. -/
theorem vn_le_log_card {n : Type*} [Fintype n] [DecidableEq n] {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef)
    (htr : ρ.trace = 1) : QAlgorithms.vnEntropy ρ ≤ Real.log (Fintype.card n) / Real.log 2 := by
  have hsum : ∑ i, hρ.1.eigenvalues i = 1 := by rw [← trace_eig hρ.1, htr]; simp
  have hc : (0 : ℝ) < Fintype.card n := by
    rcases Nat.eq_zero_or_pos (Fintype.card n) with h | h
    · exfalso; rw [Fintype.card_eq_zero_iff] at h; haveI := h; simp at hsum
    · exact_mod_cast h
  have hc' := hc.ne'
  rw [vn_eq hρ.1]
  refine div_le_div_of_nonneg_right ?_ (Real.log_nonneg one_le_two)
  have hJ := Real.concaveOn_negMulLog.le_map_sum (t := Finset.univ)
    (w := fun _ => (1 : ℝ) / Fintype.card n) (p := hρ.1.eigenvalues) (fun _ _ => by positivity)
    (by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp)
    (fun i _ => Set.mem_Ici.mpr (hρ.eigenvalues_nonneg i))
  simp only [smul_eq_mul, ← Finset.mul_sum, hsum, mul_one] at hJ
  have h2 : Real.negMulLog (1 / (Fintype.card n : ℝ)) =
      1 / Fintype.card n * Real.log (Fintype.card n) := by
    simp [Real.negMulLog, Real.log_inv]
  rw [h2] at hJ
  exact le_of_mul_le_mul_left hJ (by positivity)


lemma vn_conjT {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (W : Matrix m n ℂ) : QAlgorithms.vnEntropy ((Wᴴ * W)ᵀ) = QAlgorithms.vnEntropy (W * Wᴴ) := by
  have hT : (Wᴴ * W)ᵀ.IsHermitian := (isHermitian_conjTranspose_mul_self _).transpose
  rw [vn_eq_roots hT, Matrix.charpoly_transpose, ← vn_eq_roots (isHermitian_conjTranspose_mul_self _)]
  exact vn_mul_comm _ _ (isHermitian_conjTranspose_mul_self _) (isHermitian_mul_conjTranspose_self _)

lemma trace_tr_left {a b : Type} [Fintype a] [Fintype b] (M : Matrix (a × b) (a × b) ℂ) :
    (WildeQIT.partialTraceLeft M).trace = M.trace := by
  simp only [Matrix.trace, Matrix.diag, WildeQIT.partialTraceLeft, Matrix.of_apply, Fintype.sum_prod_type]
  exact Finset.sum_comm

lemma psd_tr_left {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    {M : Matrix (a × b) (a × b) ℂ} (h : M.PosSemidef) : (WildeQIT.partialTraceLeft M).PosSemidef := by
  have e : WildeQIT.partialTraceLeft M = ∑ x : a,
      (Matrix.of fun (j : b) (p : a × b) => if p = (x, j) then (1 : ℂ) else 0) * M *
        (Matrix.of fun (j : b) (p : a × b) => if p = (x, j) then (1 : ℂ) else 0)ᴴ := by
    ext i j
    simp [WildeQIT.partialTraceLeft, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [e]
  exact Matrix.posSemidef_sum _ (fun x _ => h.mul_mul_conjTranspose_same _)

lemma trace_pure' {ι : Type*} [Fintype ι] (v : ι → ℂ) (h : star v ⬝ᵥ v = 1) :
    (vecMulVec v (star v)).trace = 1 := by
  rw [← h]
  simp only [Matrix.trace, Matrix.diag, vecMulVec_apply, dotProduct, Pi.star_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

lemma trace_idTensor {r a b : Type} [Fintype r] [DecidableEq r] [Fintype a] [Fintype b] [DecidableEq a]
    (N : QChannel a b) (X : Matrix (r × a) (r × a) ℂ) :
    (WildeQIT.EADamping.idTensorApply N X).trace = X.trace := by
  unfold WildeQIT.EADamping.idTensorApply
  rw [Matrix.trace_sum]
  simp_rw [Matrix.trace_mul_cycle _ X]
  rw [← Matrix.trace_sum, ← Finset.sum_mul]
  have hsum : ∑ i, ((1 : Matrix r r ℂ) ⊗ₖ N.K i)ᴴ * ((1 : Matrix r r ℂ) ⊗ₖ N.K i) = 1 := by
    simp_rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, one_mul]
    rw [← one_kronecker_one, ← N.complete]
    ext ⟨x, w⟩ ⟨x', w'⟩
    simp [Matrix.sum_apply, kronecker_apply, Finset.mul_sum]
  rw [hsum, one_mul]

lemma psd_idTensor {r a b : Type} [Fintype r] [DecidableEq r] [Fintype a] [Fintype b] [DecidableEq a]
    (N : QChannel a b) {X : Matrix (r × a) (r × a) ℂ} (hX : X.PosSemidef) :
    (WildeQIT.EADamping.idTensorApply N X).PosSemidef := by
  unfold WildeQIT.EADamping.idTensorApply
  exact Matrix.posSemidef_sum _ (fun i _ => hX.mul_mul_conjTranspose_same _)

lemma conj_pure {m n : Type*} [Fintype n] (A : Matrix m n ℂ) (v : n → ℂ) (p q : m) :
    (A * vecMulVec v (star v) * Aᴴ) p q = (A *ᵥ v) p * star ((A *ᵥ v) q) := by
  simp only [Matrix.mul_apply, vecMulVec_apply, mulVec, dotProduct, conjTranspose_apply, Pi.star_apply,
    star_sum, star_mul', Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- the `R B1 B2 × E1 E2` coefficient matrix of `|ω⟩` -/
noncomputable def Wm {k a1 b1 a2 b2 : Type} [Fintype a1] [Fintype b1] [Fintype a2] [Fintype b2]
    [DecidableEq a1] [DecidableEq a2] (N1 : QChannel a1 b1) (N2 : QChannel a2 b2)
    (ϕ : k × (a1 × a2) → ℂ) : Matrix (k × (b1 × b2)) (N1.ι × N2.ι) ℂ :=
  Matrix.of fun rb e => ∑ x : a1 × a2, N1.K e.1 rb.2.1 x.1 * N2.K e.2 rb.2.2 x.2 * ϕ (rb.1, x)

lemma omega_apply {k a1 b1 a2 b2 : Type} [Fintype k] [Fintype a1] [Fintype b1] [Fintype a2] [Fintype b2]
    [DecidableEq a1] [DecidableEq a2] (N1 : QChannel a1 b1) (N2 : QChannel a2 b2)
    (ϕ : k × (a1 × a2) → ℂ) (p q : k × ((b1 × b2) × (N1.ι × N2.ι))) :
    WildeQIT.Activation.omegaState N1 N2 ϕ p q =
      Wm N1 N2 ϕ (p.1, p.2.1) p.2.2 * star (Wm N1 N2 ϕ (q.1, q.2.1) q.2.2) := by
  obtain ⟨r, ⟨b1', b2'⟩, ⟨i1, i2⟩⟩ := p
  obtain ⟨r', ⟨c1, c2⟩, ⟨j1, j2⟩⟩ := q
  simp [WildeQIT.Activation.omegaState, vecMulVec_apply, Wm, reindex_apply, kronecker_apply,
    WildeQIT.Degradable.isometricExtension]

lemma sigma_eq {k a1 b1 a2 b2 : Type} [Fintype k] [DecidableEq k] [Fintype a1] [Fintype b1] [Fintype a2]
    [Fintype b2] [DecidableEq a1] [DecidableEq a2] (N1 : QChannel a1 b1) (N2 : QChannel a2 b2)
    (ϕ : k × (a1 × a2) → ℂ) :
    WildeQIT.EADamping.idTensorApply (WildeQIT.Degradable.tensorChannel N1 N2) (vecMulVec ϕ (star ϕ)) =
      Wm N1 N2 ϕ * (Wm N1 N2 ϕ)ᴴ := by
  have h : ∀ (e : (WildeQIT.Degradable.tensorChannel N1 N2).ι) (s : k × (b1 × b2)),
      (((1 : Matrix k k ℂ) ⊗ₖ (WildeQIT.Degradable.tensorChannel N1 N2).K e) *ᵥ ϕ) s
      = Wm N1 N2 ϕ s e := by
    intro e s
    simp [mulVec, dotProduct, kronecker_apply, Matrix.one_apply, Fintype.sum_prod_type, Wm,
      WildeQIT.Degradable.tensorChannel, ite_mul]
    rfl
  ext p q
  rw [WildeQIT.EADamping.idTensorApply, Matrix.sum_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [conj_pure, h, h]; rfl

lemma margB {k a1 b1 a2 b2 : Type} [Fintype k] [Fintype a1] [Fintype b1] [Fintype a2] [Fintype b2]
    [DecidableEq a1] [DecidableEq a2] (N1 : QChannel a1 b1) (N2 : QChannel a2 b2)
    (ϕ : k × (a1 × a2) → ℂ) :
    WildeQIT.partialTraceRight (WildeQIT.partialTraceLeft (WildeQIT.Activation.omegaState N1 N2 ϕ)) =
      WildeQIT.partialTraceLeft (Wm N1 N2 ϕ * (Wm N1 N2 ϕ)ᴴ) := by
  ext b b'
  simp only [WildeQIT.partialTraceRight, WildeQIT.partialTraceLeft, of_apply, omega_apply, mul_apply,
    conjTranspose_apply]
  exact Finset.sum_comm

lemma margE {k a1 b1 a2 b2 : Type} [Fintype k] [Fintype a1] [Fintype b1] [Fintype a2] [Fintype b2]
    [DecidableEq a1] [DecidableEq a2] (N1 : QChannel a1 b1) (N2 : QChannel a2 b2)
    (ϕ : k × (a1 × a2) → ℂ) :
    WildeQIT.partialTraceLeft (WildeQIT.partialTraceLeft (WildeQIT.Activation.omegaState N1 N2 ϕ)) =
      ((Wm N1 N2 ϕ)ᴴ * Wm N1 N2 ϕ)ᵀ := by
  ext e e'
  simp only [WildeQIT.partialTraceLeft, of_apply, omega_apply, transpose_apply, mul_apply,
    conjTranspose_apply]
  rw [Finset.sum_comm, ← Finset.sum_product', Finset.univ_product_univ]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

end C3Aux

/-! C1 pieces (eq. 24.163). -/
namespace C1Aux
open WildeQIT C3Aux

lemma vn_half {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ} (hA : A.PosSemidef)
    (htr : A.trace = 1) :
    QAlgorithms.vnEntropy ((1/2 : ℝ) • A) = QAlgorithms.vnEntropy A / 2 + 1 / 2 := by
  have hsum : ∑ i, hA.1.eigenvalues i = 1 := by rw [← trace_eig hA.1, htr]; simp
  have hc : Continuous (fun x : ℝ => x * Real.logb 2 x) := by
    have := Real.continuous_mul_log.div_const (Real.log 2)
    refine this.congr fun x => ?_
    simp only [Real.logb]; ring
  have hsa : IsSelfAdjoint A := hA.1
  have hl : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  have key : ∀ x : ℝ, -((1/2 : ℝ) * x * Real.logb 2 ((1/2:ℝ) * x)) =
      Real.negMulLog x / Real.log 2 / 2 + x / 2 := by
    intro x
    have h1 : -((1/2 : ℝ) * x * Real.logb 2 ((1/2:ℝ) * x)) =
        Real.negMulLog (x * (1/2:ℝ)) / Real.log 2 := by
      simp only [Real.negMulLog, Real.logb]; ring_nf
    rw [h1, Real.negMulLog_mul]
    have h2 : Real.negMulLog (1/2 : ℝ) = Real.log 2 / 2 := by
      simp only [Real.negMulLog, one_div, Real.log_inv]; ring
    rw [h2]; field_simp
  rw [QAlgorithms.vnEntropy, ← cfc_comp_smul (1/2 : ℝ) _ A hc.continuousOn hsa, trace_cfc_herm hA.1,
    vn_eq hA.1, Complex.re_sum]
  simp only [Complex.ofReal_re, smul_eq_mul]
  rw [← Finset.sum_neg_distrib]
  simp only [key]
  rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div, ← Finset.sum_div, hsum]

lemma vn_blocks {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {A : Matrix m m ℂ} {B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    QAlgorithms.vnEntropy (fromBlocks A 0 0 B) = QAlgorithms.vnEntropy A + QAlgorithms.vnEntropy B := by
  have hF : (fromBlocks A 0 0 B).IsHermitian := IsHermitian.fromBlocks hA (by simp) hB
  rw [vn_eq_roots hF, vn_eq_roots hA, vn_eq_roots hB, charpoly_fromBlocks_zero₁₂,
    Polynomial.roots_mul (mul_ne_zero (charpoly_monic A).ne_zero (charpoly_monic B).ne_zero),
    Multiset.map_add, Multiset.sum_add, add_div]

lemma vn_iso_conj {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (W : Matrix m n ℂ) (hW : Wᴴ * W = 1) {D : Matrix n n ℂ} (hD : D.IsHermitian) :
    QAlgorithms.vnEntropy (W * D * Wᴴ) = QAlgorithms.vnEntropy D := by
  have h1 : (W * D * Wᴴ).IsHermitian := isHermitian_mul_mul_conjTranspose W hD
  have h2 : (Wᴴ * (W * D)).IsHermitian := by rw [← Matrix.mul_assoc, hW, Matrix.one_mul]; exact hD
  rw [vn_mul_comm (W * D) Wᴴ h1 h2, ← Matrix.mul_assoc, hW, Matrix.one_mul]

lemma herm_half {n : Type*} {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    ((1/2 : ℝ) • A).IsHermitian := by
  unfold IsHermitian; rw [conjTranspose_smul, hA.eq, star_trivial]

theorem vn_mix {m p q : Type*} [Fintype m] [DecidableEq m] [Fintype p] [DecidableEq p]
    [Fintype q] [DecidableEq q]
    (W : Matrix m (p ⊕ q) ℂ) (hW : Wᴴ * W = 1) {A : Matrix p p ℂ} {B : Matrix q q ℂ}
    (hA : A.PosSemidef) (hAt : A.trace = 1) (hB : B.PosSemidef) (hBt : B.trace = 1) :
    QAlgorithms.vnEntropy (W * fromBlocks ((1/2:ℝ) • A) 0 0 ((1/2:ℝ) • B) * Wᴴ) =
      1 + QAlgorithms.vnEntropy A / 2 + QAlgorithms.vnEntropy B / 2 := by
  have hD : (fromBlocks ((1/2:ℝ) • A) 0 0 ((1/2:ℝ) • B)).IsHermitian :=
    IsHermitian.fromBlocks (herm_half hA.1) (by simp) (herm_half hB.1)
  rw [vn_iso_conj W hW hD, vn_blocks (herm_half hA.1) (herm_half hB.1), vn_half hA hAt,
    vn_half hB hBt]
  ring

lemma hK {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] (N : QChannel a b)
    (V : Matrix b a ℂ) (e : b → ℂ)
    (hN : ∀ ρ : Matrix a a ℂ, N.apply ρ =
      (1 / 2 : ℂ) • (V * ρ * Vᴴ) + ((1 / 2 : ℂ) * ρ.trace) • vecMulVec e (star e))
    (y y' : b) (x x' : a) :
    ∑ i, N.K i y x * star (N.K i y' x') =
      (1/2 : ℂ) * (V y x * star (V y' x')) + (1/2 : ℂ) * (if x = x' then e y * star (e y') else 0) := by
  have h := congrFun (congrFun (hN (Matrix.single x x' (1:ℂ))) y) y'
  have hc : ∀ (M : Matrix b a ℂ), (M * Matrix.single x x' (1:ℂ) * Mᴴ) y y' = M y x * star (M y' x') := by
    intro M
    simp [Matrix.mul_apply, Matrix.single_apply, conjTranspose_apply, ite_and, Finset.sum_ite_eq,
      Finset.sum_ite_eq', ite_mul]
  simp only [QChannel.apply, Matrix.sum_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    vecMulVec_apply, Pi.star_apply, hc] at h
  rw [h]
  by_cases hx : x = x'
  · subst hx; simp [Matrix.trace_single_eq_same]
  · simp [Matrix.trace_single_eq_of_ne x x' (1:ℂ) hx, hx]

noncomputable def Wm2 {k a1 a2 b2 : Type} [Fintype a2] [Fintype b2] [DecidableEq a2]
    (N2 : QChannel a2 b2) (ϕ : k × (a1 × a2) → ℂ) : Matrix (k × (a1 × b2)) N2.ι ℂ :=
  Matrix.of fun s e2 => ∑ x2 : a2, N2.K e2 s.2.2 x2 * ϕ (s.1, (s.2.1, x2))

noncomputable def Wm3 {k a1 a2 b2 : Type} [Fintype a2] [Fintype b2] [DecidableEq a2]
    (N2 : QChannel a2 b2) (ϕ : k × (a1 × a2) → ℂ) : Matrix (k × b2) (a1 × N2.ι) ℂ :=
  Matrix.of fun s u => Wm2 N2 ϕ (s.1, (u.1, s.2)) u.2

noncomputable def Wfull {k a1 b1 b2 : Type} [DecidableEq k] [DecidableEq b2]
    (V : Matrix b1 a1 ℂ) (e : b1 → ℂ) :
    Matrix (k × (b1 × b2)) ((k × (a1 × b2)) ⊕ (k × b2)) ℂ :=
  Matrix.of fun i => Sum.elim (fun j => if i.1 = j.1 ∧ i.2.2 = j.2.2 then V i.2.1 j.2.1 else 0)
    (fun j => if i.1 = j.1 ∧ i.2.2 = j.2 then e i.2.1 else 0)

lemma Wm_eq {k a1 b1 a2 b2 : Type} [Fintype a1] [Fintype b1] [Fintype a2] [Fintype b2]
    [DecidableEq a1] [DecidableEq a2] (N1 : QChannel a1 b1) (N2 : QChannel a2 b2)
    (ϕ : k × (a1 × a2) → ℂ) (i : k × (b1 × b2)) (e1 : N1.ι) (e2 : N2.ι) :
    Wm N1 N2 ϕ i (e1, e2) = ∑ x1 : a1, N1.K e1 i.2.1 x1 * Wm2 N2 ϕ (i.1, (x1, i.2.2)) e2 := by
  simp [Wm, Wm2, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

lemma Wfull_entry {k a1 b1 b2 : Type} [Fintype k] [DecidableEq k] [Fintype a1] [Fintype b2]
    [DecidableEq b2] (V : Matrix b1 a1 ℂ) (e : b1 → ℂ)
    (A : Matrix (k × (a1 × b2)) (k × (a1 × b2)) ℂ) (B : Matrix (k × b2) (k × b2) ℂ)
    (s s' : k) (b b' : b1) (c c' : b2) :
    (Wfull (k := k) (b2 := b2) V e * fromBlocks ((1/2:ℝ) • A) 0 0 ((1/2:ℝ) • B) * (Wfull (k := k) (b2 := b2) V e)ᴴ) (s, (b, c)) (s', (b', c')) =
      ∑ x1 : a1, ∑ x1' : a1, (2⁻¹ : ℂ) * (V b x1 * star (V b' x1')) * A (s, (x1, c)) (s', (x1', c')) +
      (2⁻¹ : ℂ) * (e b * star (e b')) * B (s, c) (s', c') := by
  rw [Matrix.mul_apply, Fintype.sum_sum_type]
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
    fromBlocks_apply₂₁, fromBlocks_apply₂₂, conjTranspose_apply, Wfull, of_apply, Sum.elim_inl,
    Sum.elim_inr, Matrix.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add,
    Matrix.smul_apply]
  simp only [Fintype.sum_prod_type, ite_and, apply_ite (starRingEnd ℂ), map_zero, mul_ite, ite_mul,
    mul_zero, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hs : ∀ (P : Prop) [Decidable P] (z : ℂ),
      (starRingEnd ℂ) (if P then z else 0) = if P then (starRingEnd ℂ) z else 0 := by
    intro P _ z; split_ifs <;> simp
  have hs' : ∀ (P : Prop) [Decidable P] (z : ℂ),
      star (if P then z else 0) = if P then star z else 0 := by
    intro P _ z; split_ifs <;> simp
  simp only [hs, hs', mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Complex.real_smul]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => by push_cast; ring
  · push_cast; ring

theorem sigma_split {k a1 b1 a2 b2 : Type} [Fintype k] [DecidableEq k] [Fintype a1] [Fintype b1]
    [Fintype a2] [Fintype b2] [DecidableEq a1] [DecidableEq a2] [DecidableEq b1] [DecidableEq b2]
    (N1 : QChannel a1 b1) (N2 : QChannel a2 b2) (ϕ : k × (a1 × a2) → ℂ)
    (V : Matrix b1 a1 ℂ) (e : b1 → ℂ)
    (hN : ∀ ρ : Matrix a1 a1 ℂ, N1.apply ρ =
      (1 / 2 : ℂ) • (V * ρ * Vᴴ) + ((1 / 2 : ℂ) * ρ.trace) • vecMulVec e (star e)) :
    Wm N1 N2 ϕ * (Wm N1 N2 ϕ)ᴴ = Wfull (k := k) (b2 := b2) V e * fromBlocks ((1/2:ℝ) • (Wm2 N2 ϕ * (Wm2 N2 ϕ)ᴴ)) 0 0
      ((1/2:ℝ) • (Wm3 N2 ϕ * (Wm3 N2 ϕ)ᴴ)) * (Wfull (k := k) (b2 := b2) V e)ᴴ := by
  ext ⟨s, b1, c⟩ ⟨s', b1', c'⟩
  have L : (Wm N1 N2 ϕ * (Wm N1 N2 ϕ)ᴴ) (s, (b1, c)) (s', (b1', c')) =
      ∑ e2 : N2.ι, ∑ x1 : a1, ∑ x1' : a1,
        (∑ e1 : N1.ι, N1.K e1 b1 x1 * star (N1.K e1 b1' x1')) *
        (Wm2 N2 ϕ (s, (x1, c)) e2 * star (Wm2 N2 ϕ (s', (x1', c')) e2)) := by
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    refine Finset.sum_comm.trans ?_
    refine Finset.sum_congr rfl fun e2 _ => ?_
    simp only [conjTranspose_apply, Wm_eq, star_sum, star_mul', Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_comm.trans ?_
    refine (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans ?_
    refine Finset.sum_comm.trans ?_
    refine Finset.sum_congr rfl fun x1 _ => Finset.sum_congr rfl fun x1' _ => ?_
    exact Finset.sum_congr rfl fun e1 _ => by ring
  rw [L, Wfull_entry]
  simp only [hK N1 V e hN, add_mul, Finset.sum_add_distrib, Matrix.mul_apply, conjTranspose_apply,
    Wm3, of_apply, Fintype.sum_prod_type, mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, Finset.mul_sum]
  congr 1
  · refine Finset.sum_comm.trans ?_
    refine Finset.sum_congr rfl fun x1 _ => ?_
    refine Finset.sum_comm.trans ?_
    exact Finset.sum_congr rfl fun x1' _ => Finset.sum_congr rfl fun e2 _ => by ring
  · refine Finset.sum_comm.trans ?_
    exact Finset.sum_congr rfl fun x1 _ => Finset.sum_congr rfl fun e2 _ => by ring


lemma star_ite0 (P : Prop) [Decidable P] (z : ℂ) :
    star (if P then z else 0) = if P then star z else 0 := by
  split_ifs <;> simp

/-- the `B1B2` (reference-free) version of `Wfull` -/
noncomputable def W0 {a1 b1 b2 : Type} [DecidableEq b2] (V : Matrix b1 a1 ℂ) (e : b1 → ℂ) :
    Matrix (b1 × b2) ((a1 × b2) ⊕ b2) ℂ :=
  Matrix.of fun i => Sum.elim (fun j => if i.2 = j.2 then V i.1 j.1 else 0)
    (fun j => if i.2 = j then e i.1 else 0)

lemma W0_entry {a1 b1 b2 : Type} [Fintype a1] [Fintype b2]
    [DecidableEq b2] (V : Matrix b1 a1 ℂ) (e : b1 → ℂ)
    (A : Matrix (a1 × b2) (a1 × b2) ℂ) (B : Matrix b2 b2 ℂ) (b b' : b1) (c c' : b2) :
    (W0 (b2 := b2) V e * fromBlocks ((1/2:ℝ) • A) 0 0 ((1/2:ℝ) • B) * (W0 (b2 := b2) V e)ᴴ) (b, c) (b', c') =
      ∑ x1 : a1, ∑ x1' : a1, (2⁻¹ : ℂ) * (V b x1 * star (V b' x1')) * A (x1, c) (x1', c') +
      (2⁻¹ : ℂ) * (e b * star (e b')) * B c c' := by
  rw [Matrix.mul_apply, Fintype.sum_sum_type]
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
    fromBlocks_apply₂₁, fromBlocks_apply₂₂, conjTranspose_apply, W0, of_apply, Sum.elim_inl,
    Sum.elim_inr, Matrix.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add,
    Matrix.smul_apply]
  simp only [Fintype.sum_prod_type, star_ite0, map_zero, mul_ite, ite_mul,
    mul_zero, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Complex.real_smul]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => by push_cast; ring
  · push_cast; ring

lemma iso_facts {a1 b1 : Type} [Fintype a1] [Fintype b1] [DecidableEq a1] (V : Matrix b1 a1 ℂ)
    (e : b1 → ℂ) (hV : Vᴴ * V = 1) (he : star e ⬝ᵥ e = 1) (hVe : Vᴴ *ᵥ e = 0) :
    (∀ x x', ∑ b, star (V b x) * V b x' = if x = x' then 1 else 0) ∧
    (∑ b, star (e b) * e b = 1) ∧ (∀ x, ∑ b, star (V b x) * e b = 0) ∧
    (∀ x, ∑ b, star (e b) * V b x = 0) := by
  have h3 : ∀ x, ∑ b, star (V b x) * e b = 0 := fun x => by
    have := congrFun hVe x; simpa [Matrix.mulVec, dotProduct] using this
  refine ⟨fun x x' => ?_, by simpa [dotProduct] using he, h3, fun x => ?_⟩
  · have := congrFun (congrFun hV x) x'; simpa [Matrix.mul_apply, Matrix.one_apply] using this
  · have := congrArg star (h3 x)
    rw [star_sum] at this
    simpa [mul_comm] using this

lemma W0_iso {a1 b1 b2 : Type} [Fintype a1] [Fintype b1] [Fintype b2] [DecidableEq a1]
    [DecidableEq b2] (V : Matrix b1 a1 ℂ) (e : b1 → ℂ) (hV : Vᴴ * V = 1) (he : star e ⬝ᵥ e = 1)
    (hVe : Vᴴ *ᵥ e = 0) : (W0 (b2 := b2) V e)ᴴ * W0 (b2 := b2) V e = 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := iso_facts V e hV he hVe
  ext (⟨x, c⟩ | c) (⟨x', c'⟩ | c') <;>
  simp only [Matrix.mul_apply, conjTranspose_apply, W0, of_apply, Sum.elim_inl, Sum.elim_inr,
    Fintype.sum_prod_type, Matrix.one_apply, star_ite0, mul_ite, ite_mul, mul_zero, zero_mul,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, if_false] <;>
  first
    | (rw [Finset.sum_comm]; simp only [Finset.sum_ite_irrel, Finset.sum_const_zero,
        Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true])
    | skip <;>
  simp only [h1, h2, h3, h4, Prod.mk.injEq] <;> split_ifs <;> simp_all

lemma Wfull_iso {k a1 b1 b2 : Type} [Fintype k] [DecidableEq k] [Fintype a1] [Fintype b1]
    [Fintype b2] [DecidableEq a1] [DecidableEq b2] (V : Matrix b1 a1 ℂ) (e : b1 → ℂ)
    (hV : Vᴴ * V = 1) (he : star e ⬝ᵥ e = 1) (hVe : Vᴴ *ᵥ e = 0) :
    (Wfull (k := k) (b2 := b2) V e)ᴴ * Wfull (k := k) (b2 := b2) V e = 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := iso_facts V e hV he hVe
  ext (⟨s, x, c⟩ | ⟨s, c⟩) (⟨s', x', c'⟩ | ⟨s', c'⟩) <;>
  simp only [Matrix.mul_apply, conjTranspose_apply, Wfull, of_apply, Sum.elim_inl, Sum.elim_inr,
    Fintype.sum_prod_type, Matrix.one_apply, ite_and, star_ite0, mul_ite, ite_mul, mul_zero, zero_mul,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, if_false] <;>
  first
    | (rw [Finset.sum_comm]; simp only [Finset.sum_ite_irrel, Finset.sum_const_zero,
        Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true])
    | skip <;>
  simp only [h1, h2, h3, h4, Prod.mk.injEq] <;> split_ifs <;> simp_all

theorem trR_split {k a1 b1 a2 b2 : Type} [Fintype k] [DecidableEq k] [Fintype a1] [Fintype b1]
    [Fintype a2] [Fintype b2] [DecidableEq a1] [DecidableEq a2] [DecidableEq b1] [DecidableEq b2]
    (N1 : QChannel a1 b1) (N2 : QChannel a2 b2) (ϕ : k × (a1 × a2) → ℂ)
    (V : Matrix b1 a1 ℂ) (e : b1 → ℂ)
    (hN : ∀ ρ : Matrix a1 a1 ℂ, N1.apply ρ =
      (1 / 2 : ℂ) • (V * ρ * Vᴴ) + ((1 / 2 : ℂ) * ρ.trace) • vecMulVec e (star e)) :
    partialTraceLeft (Wm N1 N2 ϕ * (Wm N1 N2 ϕ)ᴴ) = W0 (b2 := b2) V e *
      fromBlocks ((1/2:ℝ) • partialTraceLeft (Wm2 N2 ϕ * (Wm2 N2 ϕ)ᴴ)) 0 0
      ((1/2:ℝ) • partialTraceLeft (Wm3 N2 ϕ * (Wm3 N2 ϕ)ᴴ)) * (W0 (b2 := b2) V e)ᴴ := by
  rw [sigma_split N1 N2 ϕ V e hN]
  ext ⟨b, c⟩ ⟨b', c'⟩
  rw [W0_entry]
  simp only [partialTraceLeft, of_apply, Wfull_entry, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  refine Finset.sum_comm.trans ?_
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

lemma tr_Wm2 {k a1 a2 b2 : Type} [Fintype k] [DecidableEq k] [Fintype a1] [DecidableEq a1]
    [Fintype a2] [Fintype b2] [DecidableEq a2] (N2 : QChannel a2 b2) (ϕ : k × (a1 × a2) → ℂ)
    (hϕ : star ϕ ⬝ᵥ ϕ = 1) : (Wm2 N2 ϕ * (Wm2 N2 ϕ)ᴴ).trace = 1 := by
  set ϕ' : (k × a1) × a2 → ℂ := fun p => ϕ (p.1.1, (p.1.2, p.2)) with hϕ'd
  have hϕ' : star ϕ' ⬝ᵥ ϕ' = 1 := by
    rw [← hϕ]; simp only [dotProduct, Fintype.sum_prod_type, ϕ', Pi.star_apply]
  have key : (WildeQIT.EADamping.idTensorApply N2 (vecMulVec ϕ' (star ϕ'))).trace = 1 := by
    rw [trace_idTensor, trace_pure' _ hϕ']
  rw [← key]
  have h : ∀ (e : N2.ι) (s : (k × a1) × b2),
      (((1 : Matrix (k × a1) (k × a1) ℂ) ⊗ₖ N2.K e) *ᵥ ϕ') s = Wm2 N2 ϕ (s.1.1, (s.1.2, s.2)) e := by
    intro e s
    simp [mulVec, dotProduct, kronecker_apply, Matrix.one_apply, Fintype.sum_prod_type, Wm2, ite_mul,
      ϕ']
  simp only [Matrix.trace, Matrix.diag, WildeQIT.EADamping.idTensorApply, Matrix.sum_apply]
  simp only [conj_pure, h]
  simp only [Matrix.mul_apply, conjTranspose_apply, Fintype.sum_prod_type]

lemma tr_Wm3 {k a1 a2 b2 : Type} [Fintype k] [Fintype a1] [Fintype a2] [Fintype b2]
    [DecidableEq a2] (N2 : QChannel a2 b2) (ϕ : k × (a1 × a2) → ℂ) :
    (Wm3 N2 ϕ * (Wm3 N2 ϕ)ᴴ).trace = (Wm2 N2 ϕ * (Wm2 N2 ϕ)ᴴ).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, conjTranspose_apply, Wm3, of_apply,
    Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

open Classical in
/-- LHS of eq. (24.163) splits into the two halves of the 50% erasure. -/
theorem lhs_split {k a1 b1 a2 b2 : Type} [Fintype k] [DecidableEq k] [Fintype a1] [Fintype b1]
    [Fintype a2] [Fintype b2] [DecidableEq a1] [DecidableEq a2] [DecidableEq b1] [DecidableEq b2]
    (N1 : QChannel a1 b1) (N2 : QChannel a2 b2) (ϕ : k × (a1 × a2) → ℂ)
    (hϕ : star ϕ ⬝ᵥ ϕ = 1) (hN1 : WildeQIT.Activation.IsHalfErasure N1) :
    QAlgorithms.vnEntropy (partialTraceRight (partialTraceLeft (WildeQIT.Activation.omegaState N1 N2 ϕ))) -
      QAlgorithms.vnEntropy (partialTraceLeft (partialTraceLeft (WildeQIT.Activation.omegaState N1 N2 ϕ))) =
    (QAlgorithms.vnEntropy (partialTraceLeft (Wm2 N2 ϕ * (Wm2 N2 ϕ)ᴴ)) -
        QAlgorithms.vnEntropy (Wm2 N2 ϕ * (Wm2 N2 ϕ)ᴴ)) / 2 +
      (QAlgorithms.vnEntropy (partialTraceLeft (Wm3 N2 ϕ * (Wm3 N2 ϕ)ᴴ)) -
        QAlgorithms.vnEntropy (Wm3 N2 ϕ * (Wm3 N2 ϕ)ᴴ)) / 2 := by
  obtain ⟨V, e, hV, he, hVe, hN⟩ := hN1
  have p2 := posSemidef_self_mul_conjTranspose (Wm2 N2 ϕ)
  have p3 := posSemidef_self_mul_conjTranspose (Wm3 N2 ϕ)
  have t2 := tr_Wm2 N2 ϕ hϕ
  have t3 : (Wm3 N2 ϕ * (Wm3 N2 ϕ)ᴴ).trace = 1 := (tr_Wm3 N2 ϕ).trans t2
  rw [margB, margE, vn_conjT, trR_split N1 N2 ϕ V e hN, sigma_split N1 N2 ϕ V e hN,
    vn_mix _ (W0_iso V e hV he hVe) (psd_tr_left p2) (by rw [trace_tr_left, t2])
      (psd_tr_left p3) (by rw [trace_tr_left, t3]),
    vn_mix _ (Wfull_iso V e hV he hVe) p2 t2 p3 t3]
  ring


/-! (e) the book's input `ϕ = Σ √p_x |x⟩_R |x⟩_{A1'} |φ^x⟩_{A1''A2}`. -/

lemma spec' {n : Type*} [Fintype n] [DecidableEq n] {s : Matrix n n ℂ} (hs : s.IsHermitian) :
    (hs.eigenvectorUnitary : Matrix n n ℂ) * diagonal (fun i => ((hs.eigenvalues i : ℝ) : ℂ)) *
      star (hs.eigenvectorUnitary : Matrix n n ℂ) = s := by
  have hsa : IsSelfAdjoint s := hs
  have h := cfc_id' ℝ s hsa
  rw [hs.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply] at h
  exact h

/-- purification: `ρ = Tr_Z |ψ⟩⟨ψ|` with `ψ z y = √λ_z U y z` -/
lemma purify {n : Type} [Fintype n] [DecidableEq n] {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef) :
    ∃ ψ : n → n → ℂ, ∀ y y', ∑ z, ψ z y * star (ψ z y') = ρ y y' := by
  set U : Matrix n n ℂ := (hρ.1.eigenvectorUnitary : Matrix n n ℂ) with hU
  refine ⟨fun z y => ((Real.sqrt (hρ.1.eigenvalues z) : ℝ) : ℂ) * U y z, fun y y' => ?_⟩
  have h := congrFun (congrFun (spec' hρ.1) y) y'
  rw [← h]
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.star_apply, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  refine Finset.sum_congr rfl fun z _ => ?_
  have hs : star (((Real.sqrt (hρ.1.eigenvalues z)) : ℝ) : ℂ) =
      ((Real.sqrt (hρ.1.eigenvalues z) : ℝ) : ℂ) := by simp
  have hq : ((Real.sqrt (hρ.1.eigenvalues z) : ℝ) : ℂ) * ((Real.sqrt (hρ.1.eigenvalues z) : ℝ) : ℂ) =
      ((hρ.1.eigenvalues z : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hρ.eigenvalues_nonneg z)]
  rw [star_mul', hs]
  linear_combination (U y z * star (U y' z)) * hq

/-- the book's pure input, `f : X × Z ↪ a1` embeds `A1' A1''` into `A1` -/
noncomputable def phiB {X Z a1 a2 : Type} [Fintype Z] [DecidableEq a1] (f : X × Z ↪ a1)
    (p : X → ℝ) (ψ : X → Z → a2 → ℂ) : X × (a1 × a2) → ℂ :=
  fun q => ∑ z, if q.2.1 = f (q.1, z) then ((Real.sqrt (p q.1) : ℝ) : ℂ) * ψ q.1 z q.2.2 else 0

/-- `(I ⊗ V^{N2}) |φ^x⟩` coefficients -/
noncomputable def Gm {X Z a2 b2 : Type} [Fintype a2] [Fintype b2] [DecidableEq a2]
    (N2 : QChannel a2 b2) (ψ : X → Z → a2 → ℂ) (x : X) (z : Z) (b : b2) (e : N2.ι) : ℂ :=
  ∑ y, N2.K e b y * ψ x z y

lemma L0 {X Z a1 a2 b2 : Type} [Fintype Z] [DecidableEq a1] [Fintype a2] [Fintype b2]
    [DecidableEq a2] (N2 : QChannel a2 b2) (f : X × Z ↪ a1) (p : X → ℝ) (ψ : X → Z → a2 → ℂ)
    (x : X) (a : a1) (b : b2) (e : N2.ι) :
    Wm2 N2 (phiB f p ψ) (x, (a, b)) e =
      ∑ z, if a = f (x, z) then ((Real.sqrt (p x) : ℝ) : ℂ) * Gm N2 ψ x z b e else 0 := by
  simp only [Wm2, phiB, of_apply, Finset.mul_sum, mul_ite, mul_zero]
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun z _ => ?_)
  split_ifs
  · rw [Gm, Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  · simp

lemma collapse {X Z a1 : Type} [Fintype Z] [DecidableEq X] [DecidableEq Z] [Fintype a1]
    [DecidableEq a1] (f : X × Z ↪ a1) (r r' : X) (u v : Z → ℂ) :
    ∑ a, (∑ z, if a = f (r, z) then u z else 0) * star (∑ z, if a = f (r', z) then v z else 0) =
      if r = r' then ∑ z, u z * star (v z) else 0 := by
  simp only [star_sum, star_ite0, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_comm.trans ?_
  simp only [ite_mul, mul_ite, zero_mul, mul_zero]
  simp [Finset.sum_ite_irrel, Finset.sum_ite_eq', Finset.sum_ite_eq, f.injective.eq_iff, ite_and]
  by_cases h : r = r'
  · subst h; simp
  · simp [h, Ne.symm h]

lemma L1 {X Z a1 a2 b2 : Type} [Fintype Z] [DecidableEq X] [DecidableEq Z] [Fintype a1]
    [DecidableEq a1] [Fintype a2] [Fintype b2]
    [DecidableEq a2] (N2 : QChannel a2 b2) (f : X × Z ↪ a1) (p : X → ℝ) (hp : ∀ x, 0 ≤ p x)
    (ψ : X → Z → a2 → ℂ) (r r' : X) (b b' : b2) (e e' : N2.ι) :
    ∑ a, Wm2 N2 (phiB f p ψ) (r, (a, b)) e * star (Wm2 N2 (phiB f p ψ) (r', (a, b')) e') =
      if r = r' then (p r : ℂ) * ∑ z, Gm N2 ψ r z b e * star (Gm N2 ψ r z b' e') else 0 := by
  simp only [L0]
  rw [collapse f r r' (fun z => ((Real.sqrt (p r) : ℝ) : ℂ) * Gm N2 ψ r z b e)
    (fun z => ((Real.sqrt (p r') : ℝ) : ℂ) * Gm N2 ψ r' z b' e')]
  split_ifs with h
  · subst h
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    have hs : star (((Real.sqrt (p r)) : ℝ) : ℂ) = ((Real.sqrt (p r) : ℝ) : ℂ) := by simp
    have hq : ((Real.sqrt (p r) : ℝ) : ℂ) * ((Real.sqrt (p r) : ℝ) : ℂ) = (p r : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hp r)]
    rw [star_mul', hs]
    linear_combination (Gm N2 ψ r z b e * star (Gm N2 ψ r z b' e')) * hq
  · rfl

lemma L2 {X Z a2 b2 : Type} [Fintype Z] [Fintype a2] [Fintype b2] [DecidableEq a2]
    (N2 : QChannel a2 b2) (ψ : X → Z → a2 → ℂ) (ρ : X → Matrix a2 a2 ℂ)
    (hψ : ∀ x y y', ∑ z, ψ x z y * star (ψ x z y') = ρ x y y') (r : X) (b b' : b2) (e e' : N2.ι) :
    ∑ z, Gm N2 ψ r z b e * star (Gm N2 ψ r z b' e') =
      ∑ y, ∑ y', N2.K e b y * ρ r y y' * star (N2.K e' b' y') := by
  simp only [Gm, star_sum, star_mul', Finset.sum_mul, Finset.mul_sum]
  refine Eq.trans ?_ Finset.sum_comm
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun y' _ => ?_)
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun y _ => ?_)
  rw [← hψ r y y', Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun z _ => by ring


/-! (f) the four entropy identities for the book's input. -/

lemma apply_entry {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] (N : QChannel a b)
    (ρ : Matrix a a ℂ) (y y' : b) :
    N.apply ρ y y' = ∑ i, ∑ x, ∑ x', N.K i y x * ρ x x' * star (N.K i y' x') := by
  simp only [QChannel.apply, Matrix.sum_apply, Matrix.mul_apply, conjTranspose_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_comm

lemma comp_entry {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] (N : QChannel a b)
    (ρ : Matrix a a ℂ) (i j : N.ι) :
    WildeQIT.Degradable.complementaryApply N ρ i j =
      ∑ y, ∑ x, ∑ x', N.K i y x * ρ x x' * star (N.K j y x') := by
  simp only [WildeQIT.Degradable.complementaryApply, partialTraceLeft, of_apply, Matrix.mul_apply,
    conjTranspose_apply, WildeQIT.Degradable.isometricExtension, Finset.sum_mul]
  exact Finset.sum_congr rfl fun y _ => Finset.sum_comm

lemma phiB_norm {X Z a1 a2 : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
    [Fintype a1] [DecidableEq a1] [Fintype a2] [DecidableEq a2]
    (f : X × Z ↪ a1) (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (ψ : X → Z → a2 → ℂ) (ρ : X → Matrix a2 a2 ℂ)
    (hψ : ∀ x y y', ∑ z, ψ x z y * star (ψ x z y') = ρ x y y') (htr : ∀ x, (ρ x).trace = 1) :
    star (phiB f p ψ) ⬝ᵥ phiB f p ψ = 1 := by
  have key : ∀ x y, ∑ a, phiB f p ψ (x, (a, y)) * star (phiB f p ψ (x, (a, y))) =
      (p x : ℂ) * ρ x y y := by
    intro x y
    simp only [phiB]
    rw [collapse f x x (fun z => ((Real.sqrt (p x) : ℝ) : ℂ) * ψ x z y)
      (fun z => ((Real.sqrt (p x) : ℝ) : ℂ) * ψ x z y), if_pos rfl, ← hψ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    have hs : star (((Real.sqrt (p x)) : ℝ) : ℂ) = ((Real.sqrt (p x) : ℝ) : ℂ) := by simp
    have hq : ((Real.sqrt (p x) : ℝ) : ℂ) * ((Real.sqrt (p x) : ℝ) : ℂ) = (p x : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hp x)]
    rw [star_mul', hs]
    linear_combination (ψ x z y * star (ψ x z y)) * hq
  have h2 : star (phiB f p ψ) ⬝ᵥ phiB f p ψ =
      ∑ x, ∑ y, ∑ a, phiB f p ψ (x, (a, y)) * star (phiB f p ψ (x, (a, y))) := by
    simp only [dotProduct, Pi.star_apply, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [h2]
  simp only [key, ← Finset.mul_sum]
  have h3 : ∀ x, ∑ y, ρ x y y = 1 := fun x => by simpa [Matrix.trace] using htr x
  simp only [h3, mul_one]
  exact_mod_cast hp1

lemma S3_eq {X Z a1 a2 b2 : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
    [Fintype a1] [DecidableEq a1] [Fintype a2] [DecidableEq a2] [Fintype b2] [DecidableEq b2]
    (N2 : QChannel a2 b2) (f : X × Z ↪ a1) (p : X → ℝ) (hp : ∀ x, 0 ≤ p x)
    (ψ : X → Z → a2 → ℂ) (ρ : X → Matrix a2 a2 ℂ)
    (hψ : ∀ x y y', ∑ z, ψ x z y * star (ψ x z y') = ρ x y y') :
    Wm3 N2 (phiB f p ψ) * (Wm3 N2 (phiB f p ψ))ᴴ =
      WildeQIT.Degradable.cqState p (fun x => N2.apply (ρ x)) := by
  ext ⟨r, b⟩ ⟨r', b'⟩
  simp only [C2Aux.cq_apply, apply_entry]
  simp only [Matrix.mul_apply, conjTranspose_apply, Wm3, of_apply, Fintype.sum_prod_type]
  conv_lhs => rw [Finset.sum_comm]
  simp only [L1 N2 f p hp ψ, L2 N2 ψ ρ hψ]
  by_cases h : r = r'
  · subst h; simp only [eq_self_iff_true, if_true, ↓reduceIte, Finset.mul_sum]
  · simp [h]

lemma S2_gram {X Z a1 a2 b2 : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
    [Fintype a1] [DecidableEq a1] [Fintype a2] [DecidableEq a2] [Fintype b2] [DecidableEq b2]
    (N2 : QChannel a2 b2) (f : X × Z ↪ a1) (p : X → ℝ) (hp : ∀ x, 0 ≤ p x)
    (ψ : X → Z → a2 → ℂ) (ρ : X → Matrix a2 a2 ℂ)
    (hψ : ∀ x y y', ∑ z, ψ x z y * star (ψ x z y') = ρ x y y') :
    (Wm2 N2 (phiB f p ψ))ᴴ * Wm2 N2 (phiB f p ψ) =
      (∑ x, p x • WildeQIT.Degradable.complementaryApply N2 (ρ x))ᵀ := by
  ext e e'
  rw [transpose_apply, Matrix.sum_apply]
  simp only [Matrix.smul_apply, comp_entry, Complex.real_smul]
  simp only [Matrix.mul_apply, conjTranspose_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun r _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  have hc : ∀ b, ∑ a, star (Wm2 N2 (phiB f p ψ) (r, (a, b)) e) * Wm2 N2 (phiB f p ψ) (r, (a, b)) e' =
      ∑ a, Wm2 N2 (phiB f p ψ) (r, (a, b)) e' * star (Wm2 N2 (phiB f p ψ) (r, (a, b)) e) :=
    fun b => Finset.sum_congr rfl fun _ _ => mul_comm _ _
  simp only [hc, L1 N2 f p hp ψ, L2 N2 ψ ρ hψ, eq_self_iff_true, if_true, ↓reduceIte, Finset.mul_sum]

noncomputable def Mt {X a1 a2 b2 : Type} [Fintype a2] [Fintype b2] [DecidableEq a2]
    (N2 : QChannel a2 b2) (ϕ : X × (a1 × a2) → ℂ) : Matrix (a1 × b2) (X × N2.ι) ℂ :=
  Matrix.of fun ab re => Wm2 N2 ϕ (re.1, ab) re.2

lemma trS2_eq {X a1 a2 b2 : Type} [Fintype X] [Fintype a2] [Fintype b2] [DecidableEq a2]
    (N2 : QChannel a2 b2) (ϕ : X × (a1 × a2) → ℂ) :
    partialTraceLeft (Wm2 N2 ϕ * (Wm2 N2 ϕ)ᴴ) = Mt N2 ϕ * (Mt N2 ϕ)ᴴ := by
  ext ab ab'
  simp only [partialTraceLeft, of_apply, Matrix.mul_apply, conjTranspose_apply, Mt,
    Fintype.sum_prod_type]

open Classical in
lemma Mt_gram {X Z a1 a2 b2 : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
    [Fintype a1] [DecidableEq a1] [Fintype a2] [DecidableEq a2] [Fintype b2] [DecidableEq b2]
    (N2 : QChannel a2 b2) (f : X × Z ↪ a1) (p : X → ℝ) (hp : ∀ x, 0 ≤ p x)
    (ψ : X → Z → a2 → ℂ) (ρ : X → Matrix a2 a2 ℂ)
    (hψ : ∀ x y y', ∑ z, ψ x z y * star (ψ x z y') = ρ x y y') :
    (Mt N2 (phiB f p ψ))ᴴ * Mt N2 (phiB f p ψ) =
      (WildeQIT.Degradable.cqState p (fun x => WildeQIT.Degradable.complementaryApply N2 (ρ x)))ᵀ := by
  ext ⟨r, e⟩ ⟨r', e'⟩
  simp only [transpose_apply, C2Aux.cq_apply, comp_entry]
  simp only [Matrix.mul_apply, conjTranspose_apply, Mt, of_apply, Fintype.sum_prod_type]
  conv_lhs => rw [Finset.sum_comm]
  have hc : ∀ b, ∑ a, star (Wm2 N2 (phiB f p ψ) (r, (a, b)) e) * Wm2 N2 (phiB f p ψ) (r', (a, b)) e' =
      ∑ a, Wm2 N2 (phiB f p ψ) (r', (a, b)) e' * star (Wm2 N2 (phiB f p ψ) (r, (a, b)) e) :=
    fun b => Finset.sum_congr rfl fun _ _ => mul_comm _ _
  simp only [hc, L1 N2 f p hp ψ, L2 N2 ψ ρ hψ]
  by_cases h : r' = r
  · subst h; simp only [eq_self_iff_true, if_true, ↓reduceIte, Finset.mul_sum]
  · simp [h]

open Classical in
theorem c1_value {X Z a1 a2 b2 : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
    [Fintype a1] [DecidableEq a1] [Fintype a2] [DecidableEq a2] [Fintype b2] [DecidableEq b2]
    (N2 : QChannel a2 b2) (f : X × Z ↪ a1) (p : X → ℝ) (hp : ∀ x, 0 ≤ p x)
    (ψ : X → Z → a2 → ℂ) (ρ : X → Matrix a2 a2 ℂ)
    (hψ : ∀ x y y', ∑ z, ψ x z y * star (ψ x z y') = ρ x y y')
    (hH : ∀ x, (ρ x).IsHermitian) (ht : ∀ x, (ρ x).trace = 1) :
    (QAlgorithms.vnEntropy (partialTraceLeft (Wm2 N2 (phiB f p ψ) * (Wm2 N2 (phiB f p ψ))ᴴ)) -
        QAlgorithms.vnEntropy (Wm2 N2 (phiB f p ψ) * (Wm2 N2 (phiB f p ψ))ᴴ)) / 2 +
      (QAlgorithms.vnEntropy (partialTraceLeft (Wm3 N2 (phiB f p ψ) * (Wm3 N2 (phiB f p ψ))ᴴ)) -
        QAlgorithms.vnEntropy (Wm3 N2 (phiB f p ψ) * (Wm3 N2 (phiB f p ψ))ᴴ)) / 2 =
    (QAlgorithms.vnEntropy (∑ x, p x • N2.apply (ρ x)) -
        QAlgorithms.vnEntropy (∑ x, p x • WildeQIT.Degradable.complementaryApply N2 (ρ x)) -
        ∑ x, p x * (QAlgorithms.vnEntropy (N2.apply (ρ x)) -
          QAlgorithms.vnEntropy (WildeQIT.Degradable.complementaryApply N2 (ρ x)))) / 2 := by
  have hA : ∀ x, (N2.apply (ρ x)).IsHermitian := fun x => C2Aux.herm_apply N2 (hH x)
  have hAt : ∀ x, (N2.apply (ρ x)).trace = 1 := fun x => (C2Aux.tr_apply N2 _).trans (ht x)
  have hC : ∀ x, (WildeQIT.Degradable.complementaryApply N2 (ρ x)).IsHermitian :=
    fun x => C2Aux.herm_comp N2 (hH x)
  have hCt : ∀ x, (WildeQIT.Degradable.complementaryApply N2 (ρ x)).trace = 1 :=
    fun x => (C2Aux.tr_comp N2 _).trans (ht x)
  have e1 : QAlgorithms.vnEntropy (partialTraceLeft (Wm2 N2 (phiB f p ψ) * (Wm2 N2 (phiB f p ψ))ᴴ)) =
      (∑ x, Real.negMulLog (p x)) / Real.log 2 +
        ∑ x, p x * QAlgorithms.vnEntropy (WildeQIT.Degradable.complementaryApply N2 (ρ x)) := by
    rw [trS2_eq, ← vn_conjT, Mt_gram N2 f p hp ψ ρ hψ, transpose_transpose, C2Aux.vn_cq _ _ hC hCt]
  have e2 : QAlgorithms.vnEntropy (Wm2 N2 (phiB f p ψ) * (Wm2 N2 (phiB f p ψ))ᴴ) =
      QAlgorithms.vnEntropy (∑ x, p x • WildeQIT.Degradable.complementaryApply N2 (ρ x)) := by
    rw [← vn_conjT, S2_gram N2 f p hp ψ ρ hψ, transpose_transpose]
  have e3 : QAlgorithms.vnEntropy (partialTraceLeft (Wm3 N2 (phiB f p ψ) * (Wm3 N2 (phiB f p ψ))ᴴ)) =
      QAlgorithms.vnEntropy (∑ x, p x • N2.apply (ρ x)) := by
    rw [S3_eq N2 f p hp ψ ρ hψ, C2Aux.ptl_cq]
  have e4 : QAlgorithms.vnEntropy (Wm3 N2 (phiB f p ψ) * (Wm3 N2 (phiB f p ψ))ᴴ) =
      (∑ x, Real.negMulLog (p x)) / Real.log 2 + ∑ x, p x * QAlgorithms.vnEntropy (N2.apply (ρ x)) := by
    rw [S3_eq N2 f p hp ψ ρ hψ, C2Aux.vn_cq _ _ hA hAt]
  rw [e1, e2, e3, e4]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

open Classical in
theorem c1 {a2 b2 : Type} [Fintype a2] [DecidableEq a2] [Fintype b2] [DecidableEq b2]
    (N2 : QChannel a2 b2) (E : WildeQIT.Degradable.CQInput a2) {a1 b1 : Type} [Fintype a1]
    [DecidableEq a1] [Fintype b1] [DecidableEq b1]
    (N1 : QChannel a1 b1) (hN : WildeQIT.Activation.IsHalfErasure N1)
    (hk : E.k * Fintype.card a2 ≤ Fintype.card a1) :
    ∃ ϕ : WildeQIT.Activation.PureInput (a1 × a2),
      QAlgorithms.vnEntropy (partialTraceRight (partialTraceLeft
          (WildeQIT.Activation.omegaState N1 N2 ϕ.vec))) -
        QAlgorithms.vnEntropy (partialTraceLeft (partialTraceLeft
          (WildeQIT.Activation.omegaState N1 N2 ϕ.vec))) =
        WildeQIT.Activation.privateInfoEnsemble N2 E / 2 := by
  obtain ⟨f⟩ : Nonempty (Fin E.k × a2 ↪ a1) :=
    Function.Embedding.nonempty_of_card_le (by rw [Fintype.card_prod, Fintype.card_fin]; exact hk)
  choose ψ hψ using fun x => purify (E.isDensity x).1
  have hH : ∀ x, (E.ρ x).IsHermitian := fun x => (E.isDensity x).1.isHermitian
  have ht : ∀ x, (E.ρ x).trace = 1 := fun x => (E.isDensity x).2
  have hn := phiB_norm f E.p.prob E.p.nonneg E.p.sum_eq_one ψ E.ρ hψ ht
  refine ⟨⟨E.k, phiB f E.p.prob ψ, hn⟩, ?_⟩
  dsimp only
  rw [lhs_split N1 N2 _ hn hN, c1_value N2 f E.p.prob E.p.nonneg ψ E.ρ hψ hH ht, C2Aux.P_eq]

end C1Aux

namespace C2Aux
open WildeQIT

open Classical in
theorem c2 {a2 b2 : Type} [Fintype a2] [DecidableEq a2] [Fintype b2] [DecidableEq b2]
    (N : QChannel a2 b2) : ∃ m : ℕ, ∀ E : WildeQIT.Degradable.CQInput a2,
      ∃ E' : WildeQIT.Degradable.CQInput a2, E'.k ≤ m ∧
        WildeQIT.Activation.privateInfoEnsemble N E ≤ WildeQIT.Activation.privateInfoEnsemble N E' := by
  refine ⟨Module.finrank ℝ (Matrix b2 b2 ℂ × Matrix N.ι N.ι ℂ × ℝ) + 1, fun E => ?_⟩
  let v : Fin E.k → Matrix b2 b2 ℂ × Matrix N.ι N.ι ℂ × ℝ := fun x =>
    (N.apply (E.ρ x), WildeQIT.Degradable.complementaryApply N (E.ρ x),
      QAlgorithms.vnEntropy (N.apply (E.ρ x)) -
        QAlgorithms.vnEntropy (WildeQIT.Degradable.complementaryApply N (E.ρ x)))
  have hmem : (∑ x, E.p.prob x • v x) ∈ convexHull ℝ (Set.range v) :=
    (convex_convexHull ℝ _).sum_mem (fun i _ => E.p.nonneg i) E.p.sum_eq_one
      (fun i _ => subset_convexHull ℝ _ ⟨i, rfl⟩)
  obtain ⟨ι, hι, z, w, hz, hai, hw, hw1, hzw⟩ := eq_pos_convex_span_of_mem_convexHull hmem
  have hsel : ∀ i, ∃ x, v x = z i := fun i => hz ⟨i, rfl⟩
  choose sel hsel using hsel
  have hzv : z = fun i => v (sel i) := funext fun i => (hsel i).symm
  subst hzv
  let e := Fintype.equivFin ι
  let E' : WildeQIT.Degradable.CQInput a2 :=
    ⟨Fintype.card ι, ⟨fun j => w (e.symm j), fun j => (hw _).le,
      by rw [← hw1]; exact Fintype.sum_equiv e.symm _ _ (fun _ => rfl)⟩,
      fun j => E.ρ (sel (e.symm j)), fun j => E.isDensity _⟩
  refine ⟨E', ?_, le_of_eq ?_⟩
  · have h1 := hai.card_le_finrank_succ
    have h2 := Submodule.finrank_le (vectorSpan ℝ (Set.range fun i => v (sel i)))
    show Fintype.card ι ≤ _
    omega
  · have h1 := congrArg Prod.fst hzw
    have h2 := congrArg (fun q => q.2.1) hzw
    have h3 := congrArg (fun q => q.2.2) hzw
    simp only [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, v, smul_eq_mul] at h1 h2 h3
    have s1 : ∑ j, E'.p.prob j • N.apply (E'.ρ j) = ∑ i, w i • N.apply (E.ρ (sel i)) :=
      Fintype.sum_equiv e.symm _ _ (fun _ => rfl)
    have s2 : ∑ j, E'.p.prob j • WildeQIT.Degradable.complementaryApply N (E'.ρ j) =
        ∑ i, w i • WildeQIT.Degradable.complementaryApply N (E.ρ (sel i)) :=
      Fintype.sum_equiv e.symm _ _ (fun _ => rfl)
    have s3 : ∑ j, E'.p.prob j * (QAlgorithms.vnEntropy (N.apply (E'.ρ j)) -
          QAlgorithms.vnEntropy (WildeQIT.Degradable.complementaryApply N (E'.ρ j))) =
        ∑ i, w i * (QAlgorithms.vnEntropy (N.apply (E.ρ (sel i))) -
          QAlgorithms.vnEntropy (WildeQIT.Degradable.complementaryApply N (E.ρ (sel i)))) :=
      Fintype.sum_equiv e.symm _ _ (fun _ => rfl)
    rw [P_eq, P_eq, s1, s2, s3, h1, h2, h3]


end C2Aux

open WildeQIT WildeQIT.Activation C3Aux in
open Classical in
theorem c3 {a1 b1 a2 b2 : Type} [Fintype a1] [DecidableEq a1] [Fintype b1] [DecidableEq b1]
    [Fintype a2] [DecidableEq a2] [Fintype b2] [DecidableEq b2]
    (N1 : QChannel a1 b1) (N2 : QChannel a2 b2) (ϕ : PureInput (a1 × a2)) :
      QAlgorithms.vnEntropy (partialTraceRight (partialTraceLeft (omegaState N1 N2 ϕ.vec))) -
          QAlgorithms.vnEntropy (partialTraceLeft (partialTraceLeft (omegaState N1 N2 ϕ.vec))) ≤
        coherentInfoChannel (WildeQIT.Degradable.tensorChannel N1 N2) := by
  rw [margB, margE, vn_conjT, ← sigma_eq]
  unfold coherentInfoChannel
  have bdd : BddAbove (Set.range fun φ : PureInput (a1 × a2) =>
      QAlgorithms.vnEntropy (partialTraceLeft (WildeQIT.EADamping.idTensorApply
        (WildeQIT.Degradable.tensorChannel N1 N2) (vecMulVec φ.vec (star φ.vec)))) -
      QAlgorithms.vnEntropy (WildeQIT.EADamping.idTensorApply
        (WildeQIT.Degradable.tensorChannel N1 N2) (vecMulVec φ.vec (star φ.vec)))) := by
    refine ⟨Real.log (Fintype.card (b1 × b2)) / Real.log 2, ?_⟩
    rintro _ ⟨φ, rfl⟩
    have hpsd := psd_idTensor (WildeQIT.Degradable.tensorChannel N1 N2)
      (Matrix.posSemidef_vecMulVec_self_star φ.vec)
    have htr : (WildeQIT.EADamping.idTensorApply (WildeQIT.Degradable.tensorChannel N1 N2)
        (vecMulVec φ.vec (star φ.vec))).trace = 1 := by
      rw [trace_idTensor, trace_pure' _ φ.norm_one]
    have h1 := vn_le_log_card (psd_tr_left hpsd) (by rw [trace_tr_left, htr])
    have h2 := vn_nonneg hpsd htr
    dsimp only
    linarith
  exact le_ciSup bdd ϕ

namespace WildeQIT.Activation

open Classical in
/-- C1: eq. (24.163), the first conjunct verbatim. -/
def C1 : Prop :=
  ∀ {a2 b2 : Type} [Fintype a2] [DecidableEq a2] [Fintype b2] [DecidableEq b2]
    (N2 : QChannel a2 b2),
    ∀ (E : WildeQIT.Degradable.CQInput a2) {a1 b1 : Type} [Fintype a1] [DecidableEq a1] [Fintype b1] [DecidableEq b1]
        (N1 : QChannel a1 b1), IsHalfErasure N1 → E.k * Fintype.card a2 ≤ Fintype.card a1 →
        ∃ ϕ : PureInput (a1 × a2),
          QAlgorithms.vnEntropy (partialTraceRight (partialTraceLeft (omegaState N1 N2 ϕ.vec))) -
              QAlgorithms.vnEntropy (partialTraceLeft (partialTraceLeft (omegaState N1 N2 ϕ.vec))) =
            privateInfoEnsemble N2 E / 2

/-- C2: bounded alphabet for the private information (Caratheodory). -/
def C2 : Prop :=
  ∀ {a2 b2 : Type} [Fintype a2] [DecidableEq a2] [Fintype b2] [DecidableEq b2]
    (N2 : QChannel a2 b2), ∃ m : ℕ, ∀ E : WildeQIT.Degradable.CQInput a2,
      ∃ E' : WildeQIT.Degradable.CQInput a2, E'.k ≤ m ∧
        privateInfoEnsemble N2 E ≤ privateInfoEnsemble N2 E'

open Classical in
/-- C3: the omega quantity of any pure input is at most Q(N1 ⊗ N2). -/
def C3 : Prop :=
  ∀ {a1 b1 a2 b2 : Type} [Fintype a1] [DecidableEq a1] [Fintype b1] [DecidableEq b1]
    [Fintype a2] [DecidableEq a2] [Fintype b2] [DecidableEq b2]
    (N1 : QChannel a1 b1) (N2 : QChannel a2 b2) (ϕ : PureInput (a1 × a2)),
      QAlgorithms.vnEntropy (partialTraceRight (partialTraceLeft (omegaState N1 N2 ϕ.vec))) -
          QAlgorithms.vnEntropy (partialTraceLeft (partialTraceLeft (omegaState N1 N2 ϕ.vec))) ≤
        coherentInfoChannel (WildeQIT.Degradable.tensorChannel N1 N2)

theorem empty_of_noCQ {a : Type} [Fintype a] [DecidableEq a]
    (h : IsEmpty (WildeQIT.Degradable.CQInput a)) : IsEmpty a := by
  refine ⟨fun i => h.false ⟨1, ⟨fun _ => 1, fun _ => zero_le_one, by simp⟩,
    fun _ => Matrix.single i i 1, fun _ => ⟨?_, ?_⟩⟩⟩
  · have : (Matrix.single i i (1 : ℂ)) = vecMulVec (Pi.single i 1) (star (Pi.single i 1)) := by
      ext p q
      by_cases hp : p = i <;> by_cases hq : q = i <;>
        simp [vecMulVec, Matrix.single_apply, Pi.single_apply, hp, hq] <;> aesop
    rw [this]
    exact Matrix.posSemidef_vecMulVec_self_star _
  · simp [Matrix.trace_single_eq_same]

open Classical in
theorem parent_of (h1 : C1) (h2 : C2) (h3 : C3)
    {a2 b2 : Type} [Fintype a2] [DecidableEq a2] [Fintype b2] [DecidableEq b2]
    (N2 : QChannel a2 b2) :
    (∀ (E : WildeQIT.Degradable.CQInput a2) {a1 b1 : Type} [Fintype a1] [DecidableEq a1] [Fintype b1] [DecidableEq b1]
        (N1 : QChannel a1 b1), IsHalfErasure N1 → E.k * Fintype.card a2 ≤ Fintype.card a1 →
        ∃ ϕ : PureInput (a1 × a2),
          QAlgorithms.vnEntropy (partialTraceRight (partialTraceLeft (omegaState N1 N2 ϕ.vec))) -
              QAlgorithms.vnEntropy (partialTraceLeft (partialTraceLeft (omegaState N1 N2 ϕ.vec))) =
            privateInfoEnsemble N2 E / 2) ∧
    (∃ n : ℕ, ∀ {a1 b1 : Type} [Fintype a1] [DecidableEq a1] [Fintype b1] [DecidableEq b1]
        (N1 : QChannel a1 b1), IsHalfErasure N1 → n ≤ Fintype.card a1 →
        privateInfoChannel N2 / 2 ≤ coherentInfoChannel (WildeQIT.Degradable.tensorChannel N1 N2)) := by
  refine ⟨fun E a1 b1 _ _ _ _ N1 hN hk => h1 N2 E N1 hN hk, ?_⟩
  obtain ⟨m, hm⟩ := h2 N2
  refine ⟨m * Fintype.card a2, fun {a1 b1} _ _ _ _ N1 hN hn => ?_⟩
  -- every ensemble value is at most 2Q
  have key : ∀ E : WildeQIT.Degradable.CQInput a2,
      privateInfoEnsemble N2 E ≤ 2 * coherentInfoChannel (WildeQIT.Degradable.tensorChannel N1 N2) := by
    intro E
    obtain ⟨E', hk, hle⟩ := hm E
    have hk' : E'.k * Fintype.card a2 ≤ Fintype.card a1 :=
      le_trans (Nat.mul_le_mul_right _ hk) hn
    obtain ⟨ϕ, hϕ⟩ := h1 N2 E' N1 hN hk'
    have := h3 N1 N2 ϕ
    linarith
  unfold privateInfoChannel
  rcases isEmpty_or_nonempty (WildeQIT.Degradable.CQInput a2) with he | hne
  · rw [Real.iSup_of_isEmpty]
    have ha2 := empty_of_noCQ he
    have : IsEmpty (PureInput (a1 × a2)) := ⟨fun ϕ => by
      have h := ϕ.norm_one
      have hz : star ϕ.vec ⬝ᵥ ϕ.vec = 0 := by
        simp [dotProduct]
      rw [hz] at h
      exact zero_ne_one h⟩
    unfold coherentInfoChannel
    rw [Real.iSup_of_isEmpty]
    norm_num
  · have := ciSup_le key
    linarith

end WildeQIT.Activation

open Classical WildeQIT WildeQIT.Activation in
theorem solution {a2 b2 : Type} [Fintype a2] [DecidableEq a2] [Fintype b2] [DecidableEq b2]
    (N2 : QChannel a2 b2) :
    (∀ (E : WildeQIT.Degradable.CQInput a2) {a1 b1 : Type} [Fintype a1] [DecidableEq a1] [Fintype b1] [DecidableEq b1]
        (N1 : QChannel a1 b1), IsHalfErasure N1 → E.k * Fintype.card a2 ≤ Fintype.card a1 →
        ∃ ϕ : PureInput (a1 × a2),
          QAlgorithms.vnEntropy (partialTraceRight (partialTraceLeft (omegaState N1 N2 ϕ.vec))) -
              QAlgorithms.vnEntropy (partialTraceLeft (partialTraceLeft (omegaState N1 N2 ϕ.vec))) =
            privateInfoEnsemble N2 E / 2) ∧
    (∃ n : ℕ, ∀ {a1 b1 : Type} [Fintype a1] [DecidableEq a1] [Fintype b1] [DecidableEq b1]
        (N1 : QChannel a1 b1), IsHalfErasure N1 → n ≤ Fintype.card a1 →
        privateInfoChannel N2 / 2 ≤ coherentInfoChannel (WildeQIT.Degradable.tensorChannel N1 N2)) := by
  exact WildeQIT.Activation.parent_of
    (by
      unfold WildeQIT.Activation.C1
      intro a2 b2 _ _ _ _ N2 E a1 b1 _ _ _ _ N1 hN hk
      exact C1Aux.c1 N2 E N1 hN hk)
    (by
      unfold WildeQIT.Activation.C2
      intro a2 b2 _ _ _ _ N2
      exact C2Aux.c2 N2)
    (by
      unfold WildeQIT.Activation.C3
      intro a1 b1 a2 b2 _ _ _ _ _ _ _ _ N1 N2 ϕ
      exact c3 N1 N2 ϕ)
    N2
