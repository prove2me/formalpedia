-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P38.commutingEnsemble_reduction
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T09:39:22.128668+00:00
-- url     : https://prove2.me/submissions/425bd912-fd2f-4488-9ea4-b7a7f49189c6

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P38

-- ===== P38A =====

open scoped BigOperators ComplexConjugate
open Matrix Polynomial

namespace X4P38

lemma cfc_diag {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℝ) (f : ℝ → ℝ) :
    cfc f (diagonal (fun i => (d i : ℂ))) = diagonal (fun i => (f (d i) : ℂ)) := by
  classical
  let S : Finset ℝ := Finset.univ.image d
  let p : ℝ[X] := Lagrange.interpolate S id f
  have hp : ∀ x ∈ S, p.eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (v := id) (r := f) (Set.injOn_id _) hx
  have hD : IsSelfAdjoint (diagonal (fun i => (d i : ℂ))) := by
    rw [IsSelfAdjoint, star_eq_conjTranspose, diagonal_conjTranspose]
    congr 1; funext i; simp
  have hspec : ∀ x ∈ spectrum ℝ (diagonal (fun i => (d i : ℂ))), x ∈ S := by
    intro x hx
    rw [← spectrum.preimage_algebraMap ℂ, Set.mem_preimage, spectrum_diagonal] at hx
    obtain ⟨i, hi⟩ := hx
    have : d i = x := by simpa using hi
    simp [S, ← this]
  rw [cfc_congr (g := fun x => p.eval x) (fun x hx => (hp x (hspec x hx)).symm),
    cfc_polynomial p _ hD]
  have : aeval (diagonal (fun i => (d i : ℂ))) p = diagonal (aeval (fun i => (d i : ℂ)) p) :=
    (aeval_algHom_apply (diagonalAlgHom ℝ) (fun i => (d i : ℂ)) p)
  rw [this, aeval_pi_apply]
  congr 1; funext i
  have h := aeval_algebraMap_apply ℂ (d i) p
  simp only [Complex.coe_algebraMap] at h
  rw [h, coe_aeval_eq_eval, hp _ (by simp [S] : d i ∈ S)]

theorem tr_aeval {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (p : ℝ[X]) :
    (aeval M p).trace = ∑ i ∈ Finset.range (p.natDegree + 1), (p.coeff i : ℂ) * (M ^ i).trace := by
  rw [aeval_eq_sum_range, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.trace_smul]
  simp [Complex.real_smul]

theorem tr_cfc_eq {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (M1 : Matrix ι ι ℂ) (M2 : Matrix κ κ ℂ) (h1 : M1.IsHermitian) (h2 : M2.IsHermitian)
    (h : ∀ k : ℕ, 1 ≤ k → (M1 ^ k).trace = (M2 ^ k).trace) (f : ℝ → ℝ) (hf : f 0 = 0) :
    (cfc f M1).trace = (cfc f M2).trace := by
  classical
  let S : Finset ℝ := Finset.univ.image h1.eigenvalues ∪ Finset.univ.image h2.eigenvalues ∪ {0}
  let p : ℝ[X] := Lagrange.interpolate S id f
  have hp : ∀ x ∈ S, p.eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (v := id) (r := f) (Set.injOn_id _) hx
  have e1 : cfc f M1 = cfc (fun x => p.eval x) M1 := by
    apply cfc_congr
    intro x hx
    rw [h1.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    exact (hp _ (by simp [S])).symm
  have e2 : cfc f M2 = cfc (fun x => p.eval x) M2 := by
    apply cfc_congr
    intro x hx
    rw [h2.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    exact (hp _ (by simp [S])).symm
  have h0 : p.coeff 0 = 0 := by
    rw [coeff_zero_eq_eval_zero, hp 0 (by simp [S]), hf]
  rw [e1, e2, cfc_polynomial p M1, cfc_polynomial p M2, tr_aeval, tr_aeval]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp [h0]
  · rw [h i hi]

theorem pow_mul' {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (V : Matrix ι κ ℂ) (W : Matrix κ ι ℂ) (k : ℕ) :
    (V * W) ^ (k + 1) = V * (W * V) ^ k * W := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [Matrix.mul_assoc]

theorem tr_pow_swap {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (V : Matrix ι κ ℂ) (W : Matrix κ ι ℂ) (k : ℕ) (hk : 1 ≤ k) :
    ((V * W) ^ k).trace = ((W * V) ^ k).trace := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
  rw [pow_mul', Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, ← pow_succ]


set_option linter.deprecated false in
/-- A pairwise commuting family of Hermitian complex matrices is simultaneously unitarily
diagonalizable. -/
lemma simdiagF {A B : Type} [Fintype B] [DecidableEq B] (M : A → Matrix B B ℂ)
    (hH : ∀ a, (M a).IsHermitian) (hC : ∀ a b, Commute (M a) (M b)) :
    ∃ U : Matrix B B ℂ, Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      ∀ a, ∃ c : B → ℂ, Uᴴ * M a * U = diagonal c := by
  classical
  set T : A → Module.End ℂ (EuclideanSpace ℂ B) := fun a => Matrix.toEuclideanLin (M a)
  have sT : ∀ a, (T a).IsSymmetric := fun a => (isHermitian_iff_isSymmetric).mp (hH a)
  have cT : Pairwise (Function.onFun Commute T) := by
    intro a b _
    show T a * T b = T b * T a
    ext v i
    simp only [T, Module.End.mul_apply, toEuclideanLin_apply, WithLp.ofLp_toLp,
      Matrix.mulVec_mulVec, (hC a b).eq]
  have hint0 := LinearMap.IsSymmetric.directSum_isInternal_of_pairwise_commute sT cT
  have horth0 := LinearMap.IsSymmetric.orthogonalFamily_iInf_eigenspaces sT
  set V : (A → ℂ) → Submodule ℂ (EuclideanSpace ℂ B) :=
    fun χ => ⨅ j, Module.End.eigenspace (T j) (χ j) with hV
  have hfin : {i | V i ≠ ⊥}.Finite :=
    WellFoundedGT.finite_ne_bot_of_iSupIndep hint0.submodule_iSupIndep
  let _ : Fintype {i // V i ≠ ⊥} := hfin.fintype
  have hint : DirectSum.IsInternal (fun i : {i // V i ≠ ⊥} => V i.1) :=
    DirectSum.isInternal_ne_bot_iff.mpr hint0
  have horth : OrthogonalFamily ℂ (fun i : {i // V i ≠ ⊥} => V i.1)
      fun i => (V i.1).subtypeₗᵢ := horth0.comp Subtype.val_injective
  have hn : Module.finrank ℂ (EuclideanSpace ℂ B) = Fintype.card B := finrank_euclideanSpace
  set b0 := hint.subordinateOrthonormalBasis hn horth
  set idx0 := fun j => hint.subordinateOrthonormalBasisIndex hn j horth
  have hmem0 : ∀ j, b0 j ∈ V (idx0 j).1 :=
    fun j => hint.subordinateOrthonormalBasis_subordinate hn j horth
  set eq := Fintype.equivFin B
  set b := fun j : B => b0 (eq j)
  have hbo : Orthonormal ℂ b := b0.orthonormal.comp _ eq.injective
  set U : Matrix B B ℂ := Matrix.of fun i j => b j i with hU
  have hUU : Uᴴ * U = 1 := by
    ext l j
    have := orthonormal_iff_ite.mp hbo l j
    rw [PiLp.inner_apply] at this
    simp only [Matrix.mul_apply, conjTranspose_apply, hU, Matrix.of_apply, Matrix.one_apply]
    rw [← this]
    apply Finset.sum_congr rfl; intro i _
    simp [RCLike.inner_apply, mul_comm]
  have hUU' : U * Uᴴ = 1 := mul_eq_one_comm.mp hUU
  have eig : ∀ (N : Matrix B B ℂ) (c : B → ℂ),
      (∀ j, Matrix.toEuclideanLin N (b j) = c j • b j) → Uᴴ * N * U = diagonal c := by
    intro N c hc
    have hTU : N * U = U * diagonal c := by
      ext i j
      have := congrArg (fun v => (WithLp.ofLp v) i) (hc j)
      simp only [toEuclideanLin_apply, WithLp.ofLp_toLp, WithLp.ofLp_smul, Pi.smul_apply,
        smul_eq_mul, Matrix.mulVec, dotProduct] at this
      rw [mul_diagonal, Matrix.mul_apply]
      simp only [hU, Matrix.of_apply]
      rw [this, mul_comm]
    rw [Matrix.mul_assoc, hTU, ← Matrix.mul_assoc, hUU, Matrix.one_mul]
  refine ⟨U, hUU, hUU', fun a => ⟨fun j => (idx0 (eq j)).1 a, ?_⟩⟩
  apply eig; intro j
  have := hmem0 (eq j)
  exact Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp this a)

lemma conj_pow {B : Type} [Fintype B] [DecidableEq B] (U E : Matrix B B ℂ) (hU : Uᴴ * U = 1)
    (k : ℕ) : (U * E * Uᴴ) ^ (k + 1) = U * E ^ (k + 1) * Uᴴ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, pow_succ E (k + 1)]
    calc U * E ^ (k + 1) * Uᴴ * (U * E * Uᴴ) = U * E ^ (k + 1) * (Uᴴ * U) * E * Uᴴ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hU, Matrix.mul_one]; simp only [Matrix.mul_assoc]

lemma tn_conj {B : Type} [Fintype B] [DecidableEq B] (U : Matrix B B ℂ) (hU : Uᴴ * U = 1)
    (hU' : U * Uᴴ = 1) (d : B → ℝ) :
    (cfc Real.sqrt ((U * diagonal (fun b => (d b : ℂ)) * Uᴴ)ᴴ * (U * diagonal (fun b => (d b : ℂ)) * Uᴴ))).trace.re
      = ∑ b, |d b| := by
  set D := diagonal (fun b => (d b : ℂ))
  have hD : Dᴴ = D := by
    simp only [D, diagonal_conjTranspose]; congr 1; funext i; simp
  have hsq : (U * D * Uᴴ)ᴴ * (U * D * Uᴴ) = U * diagonal (fun b => ((d b ^ 2 : ℝ) : ℂ)) * Uᴴ := by
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hD]
    have : D * D = diagonal (fun b => ((d b ^ 2 : ℝ) : ℂ)) := by
      simp only [D, diagonal_mul_diagonal]; congr 1; funext i; push_cast; ring
    calc U * (D * Uᴴ) * (U * D * Uᴴ) = U * D * (Uᴴ * U) * D * Uᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hU, Matrix.mul_one, Matrix.mul_assoc U D D, this]
  set E := diagonal (fun b => ((d b ^ 2 : ℝ) : ℂ))
  have hE : E.IsHermitian := by
    simp only [IsHermitian, E, diagonal_conjTranspose]; congr 1; funext i; simp
  have hUE : (U * E * Uᴴ).IsHermitian := by
    simp only [IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose, hE.eq, Matrix.mul_assoc]
  rw [hsq, tr_cfc_eq (U * E * Uᴴ) E hUE hE _ Real.sqrt Real.sqrt_zero, cfc_diag, trace_diagonal]
  · simp [Real.sqrt_sq_eq_abs]
  · intro k hk
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
    rw [conj_pow U E hU, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul]

end X4P38

-- ===== P38B =====

open scoped BigOperators ComplexConjugate ComplexOrder
open Matrix QAlgorithms.Papers.Independent.Support50.P38
open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)
open QAlgorithms.Papers.Independent.Frontier30.P12 (IsStochastic)

namespace X4P38

theorem main {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq B] [Nonempty A] [Nonempty B]
    (rho : A → Matrix B B ℂ) (hrho : ∀ a, QAlgorithms.IsDensityMatrix (rho a))
    (hcomm : ∀ a b, Commute (rho a) (rho b)) :
    ∃ (u : Matrix B B ℂ) (w : A → B → ℝ),
      uᴴ * u = 1 ∧ u * uᴴ = 1 ∧ IsStochastic w ∧
      (∀ a, rho a = diagonalIn u (w a)) ∧
      (∀ p q : B → ℝ, IsLaw p → IsLaw q →
        QAlgorithms.traceNorm (diagonalIn u p - diagonalIn u q) / 2 = tv p q) := by
  obtain ⟨U, hUU, hUU', hc⟩ := simdiagF rho (fun a => (hrho a).1.isHermitian) hcomm
  choose c hc using hc
  have hpsd : ∀ a j, 0 ≤ c a j := by
    intro a j
    have := ((hrho a).1.conjTranspose_mul_mul_same U).diag_nonneg (i := j)
    rwa [hc a, diagonal_apply_eq] at this
  have hre : ∀ a j, ((c a j).re : ℂ) = c a j := by
    intro a j
    have h := (Complex.nonneg_iff.mp (hpsd a j)).2
    apply Complex.ext <;> simp [← h]
  have hrep : ∀ a, rho a = U * diagonal (c a) * Uᴴ := by
    intro a
    rw [← hc a]
    calc rho a = (U * Uᴴ) * rho a * (U * Uᴴ) := by rw [hUU', Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  refine ⟨U, fun a j => (c a j).re, hUU, hUU', ?_, ?_, ?_⟩
  · intro a
    refine ⟨fun j => (Complex.nonneg_iff.mp (hpsd a j)).1, ?_⟩
    have ht := (hrho a).2
    rw [hrep a, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hUU, Matrix.one_mul, trace_diagonal] at ht
    have := congrArg Complex.re ht
    simpa [Complex.re_sum] using this
  · intro a
    rw [hrep a, diagonalIn]
    congr 2; congr 1; funext j; exact (hre a j).symm
  · intro p q _ _
    have : diagonalIn U p - diagonalIn U q = U * diagonal (fun b => ((p b - q b : ℝ) : ℂ)) * Uᴴ := by
      simp only [diagonalIn]
      rw [← Matrix.sub_mul, ← Matrix.mul_sub, diagonal_sub]
      congr 3; funext b; push_cast; ring
    rw [this, QAlgorithms.traceNorm, tn_conj U hUU hUU', tv]

end X4P38

-- ===== P38Sol =====

noncomputable section

open QAlgorithms.Papers.Independent.Support50.P38

open scoped BigOperators Matrix ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Frontier30.P12 (IsStochastic)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon labelInformation)

attribute [local instance] Classical.propDecidable

theorem solution {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq B] [Nonempty A] [Nonempty B]
    (rho : A → Matrix B B ℂ) (hrho : ∀ a, QAlgorithms.IsDensityMatrix (rho a))
    (hcomm : ∀ a b, Commute (rho a) (rho b)) :
    ∃ (u : Matrix B B ℂ) (w : A → B → ℝ),
      uᴴ * u = 1 ∧ u * uᴴ = 1 ∧ IsStochastic w ∧
      (∀ a, rho a = diagonalIn u (w a)) ∧
      (∀ p q : B → ℝ, IsLaw p → IsLaw q →
        QAlgorithms.traceNorm (diagonalIn u p - diagonalIn u q) / 2 = tv p q) :=
  X4P38.main rho hrho hcomm

end
