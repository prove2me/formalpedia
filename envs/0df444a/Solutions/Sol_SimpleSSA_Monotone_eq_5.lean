-- Prove2me | solution 1 for SimpleSSA.Monotone.eq_5
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T07:58:35.155009+00:00
-- url     : https://prove2.me/submissions/aba5ddd2-fdf9-4bca-9927-cad025031696

import Mathlib
import Definitions.Def_SimpleSSA_Monotone_Basic

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder Kronecker
open Matrix TroppMatrixConcentration

namespace SimpleSSA.Monotone.ConditionalProof

noncomputable section

/- Spectral CFC helpers adapted from the actual accepted proof of
TroppMatrixConcentration.ch8_joint_tensor_representation,
submission 2c047fcd-723d-47ab-9179-a7d2416ec82d. -/
def diagHom {n : Type*} [Fintype n] [DecidableEq n] :
    (n → ℂ) →⋆ₐ[ℂ] Matrix n n ℂ where
  toFun x := diagonal x
  map_one' := by simp
  map_mul' x y := by exact (diagonal_mul_diagonal x y).symm
  map_zero' := by simp
  map_add' x y := by simp [diagonal_add]
  commutes' r := by simp [algebraMap_eq_diagonal]
  map_star' x := by simp [star_eq_conjTranspose, diagonal_conjTranspose]

set_option backward.isDefEq.respectTransparency false in
theorem cfc_diag {n : Type*} [Fintype n] [DecidableEq n]
    (f : ℝ → ℝ) (x : n → ℝ) :
    cfc f (diagonal (fun i => (x i : ℂ))) = diagonal (fun i => (f (x i) : ℂ)) := by
  let := IsStarNormal.instContinuousFunctionalCalculus (A := n → ℂ)
  let := IsSelfAdjoint.instContinuousFunctionalCalculus (A := n → ℂ)
  let z : n → ℂ := fun i => (x i : ℂ)
  have hx : IsSelfAdjoint z := by ext; simp [z]
  have hdiag : IsSelfAdjoint (diagHom z) := hx.map diagHom
  have hc : ContinuousOn f (spectrum ℝ z) := by
    rw [Pi.spectrum_eq]
    have heq : (⋃ i, spectrum ℝ (z i)) = Set.range x := by
      change (⋃ i, spectrum ℝ (algebraMap ℝ ℂ (x i))) = _
      simp only [spectrum.scalar_eq, Set.iUnion_singleton_eq_range]
    rw [heq]
    exact Set.Finite.continuousOn (Set.finite_range _) _
  have heq := (diagHom (n := n)).map_cfc (p := IsSelfAdjoint) (q := IsSelfAdjoint) f z hc
    (by change Continuous (fun z : n → ℂ => diagonal z); fun_prop) hx hdiag
  rw [cfc_map_pi (p := IsSelfAdjoint) (q := fun _ => IsSelfAdjoint) (S := ℂ) f z (by rwa [← Pi.spectrum_eq]) hx (fun i => by change star (x i : ℂ) = (x i : ℂ); simp)] at heq
  change diagonal (fun i => cfc f (algebraMap ℝ ℂ (x i))) = cfc f (diagonal (fun i => (x i : ℂ))) at heq
  simp only [cfc_algebraMap] at heq
  exact heq.symm

set_option backward.isDefEq.respectTransparency false in
theorem cfc_diag_conj {n : Type*} [Fintype n] [DecidableEq n]
    (U : unitary (Matrix n n ℂ)) (f : ℝ → ℝ) (x : n → ℝ) :
    cfc f ((U : Matrix n n ℂ) * diagonal (fun i => (x i : ℂ)) * star (U : Matrix _ _ ℂ)) =
      (U : Matrix n n ℂ) * diagonal (fun i => (f (x i) : ℂ)) * star (U : Matrix _ _ ℂ) := by
  let φ := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) U
  have hd : IsSelfAdjoint (diagonal (fun i => (x i : ℂ))) := by
    change (diagonal (fun i => (x i : ℂ)))ᴴ = _
    simp [diagonal_conjTranspose]
  have hc : ContinuousOn f (spectrum ℝ (diagonal (fun i => (x i : ℂ)))) := by
    rw [continuousOn_iff_continuous_domRestrict]
    fun_prop
  have heq := StarAlgHomClass.map_cfc (p := IsSelfAdjoint) (q := IsSelfAdjoint)
    φ f _ hc (by change Continuous (fun M : Matrix n n ℂ => (U : Matrix n n ℂ) * M * star (U : Matrix _ _ ℂ)); fun_prop) hd (hd.map φ)
  rw [cfc_diag] at heq
  exact heq.symm

theorem conj_diag_mul {n : Type*} [Fintype n] [DecidableEq n]
    (U : unitary (Matrix n n ℂ)) (x y : n → ℝ) :
    ((U : Matrix n n ℂ) * diagonal (fun i => (x i : ℂ)) * star (U : Matrix _ _ ℂ)) *
      ((U : Matrix n n ℂ) * diagonal (fun i => (y i : ℂ)) * star (U : Matrix _ _ ℂ)) =
    (U : Matrix n n ℂ) * diagonal (fun i => ((x i * y i : ℝ) : ℂ)) * star (U : Matrix _ _ ℂ) := by
  change (Unitary.conjStarAlgAut ℂ _ U) _ * (Unitary.conjStarAlgAut ℂ _ U) _ = _
  rw [← map_mul, diagonal_mul_diagonal]
  simp only [Complex.ofReal_mul]
  rfl


def tensorU {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (U : unitary (Matrix n n ℂ)) (V : unitary (Matrix m m ℂ)) :
    unitary (Matrix (n × m) (n × m) ℂ) :=
  ⟨(U : Matrix n n ℂ) ⊗ₖ (V : Matrix m m ℂ),
    kronecker_mem_unitary U.property V.property⟩

theorem tensor_conj {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (U : unitary (Matrix n n ℂ)) (V : unitary (Matrix m m ℂ)) (a : n → ℝ) (b : m → ℝ) :
    (tensorU U V : Matrix _ _ ℂ) *
      diagonal (fun i : n × m => ((a i.1 * b i.2 : ℝ) : ℂ)) *
      star (tensorU U V : Matrix _ _ ℂ) =
    ((U : Matrix _ _ ℂ) * diagonal (fun j => (a j : ℂ)) * star (U : Matrix _ _ ℂ)) ⊗ₖ
      ((V : Matrix _ _ ℂ) * diagonal (fun j => (b j : ℂ)) * star (V : Matrix _ _ ℂ)) := by
  simp only [tensorU, star_eq_conjTranspose, conjTranspose_kronecker]
  rw [mul_kronecker_mul, mul_kronecker_mul]
  congr 2
  rw [diagonal_kronecker_diagonal]
  simp only [Complex.ofReal_mul]


/- No positive-definiteness is used below: the zero spectral value is retained. -/
set_option backward.isDefEq.respectTransparency false in
lemma cfc_tensor_scalar {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (M : Matrix A A ℂ) (hM : M.IsHermitian)
    (c : ℝ) (f : ℝ → ℝ) :
    cfc f (M ⊗ₖ ((c : ℂ) • (1 : Matrix B B ℂ))) =
      cfc (fun x => f (x * c)) M ⊗ₖ (1 : Matrix B B ℂ) := by
  let U := hM.eigenvectorUnitary
  have hs := hM.spectral_theorem
  have hf := hM.cfc_eq (fun x => f (x * c))
  simp only [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Function.comp_def,
    RCLike.ofReal_eq_complex_ofReal] at hs hf
  have hc : Matrix.diagonal (fun _ : B => (c : ℂ)) = (c : ℂ) • (1 : Matrix B B ℂ) := by
    ext i j
    simp [Matrix.diagonal, Matrix.one_apply, mul_ite]
  have ht := tensor_conj U (1 : unitary (Matrix B B ℂ)) hM.eigenvalues (fun _ => c)
  simp only [OneMemClass.coe_one, star_one, one_mul, mul_one, hc] at ht
  have hg := tensor_conj U (1 : unitary (Matrix B B ℂ))
    (fun x => f (hM.eigenvalues x * c)) (fun _ => 1)
  simp only [OneMemClass.coe_one, star_one, mul_one, Complex.ofReal_one,
    Matrix.diagonal_one] at hg
  rw [hf]
  conv_lhs => rw [hs]
  rw [← ht, cfc_diag_conj]
  exact hg

set_option backward.isDefEq.respectTransparency false in
lemma weighted_log_mul {A : Type*} [Fintype A] [DecidableEq A]
    (M : Matrix A A ℂ) (hM : M.IsHermitian) (c : ℝ) (hc : c ≠ 0) :
    M * cfc (fun x => Real.log (x * c)) M =
      M * matrixLog M + Real.log c • M := by
  have hscalar : (fun x : ℝ => x * Real.log (x * c)) =
      (fun x => x * Real.log x + Real.log c * x) := by
    funext x
    by_cases hx : x = 0
    · simp [hx]
    · rw [Real.log_mul hx hc]
      ring
  calc
    M * cfc (fun x => Real.log (x * c)) M = cfc (fun x => x * Real.log (x * c)) M := by
      rw [cfc_mul (fun x : ℝ => x) _ M (M.finite_real_spectrum.continuousOn _)
        (M.finite_real_spectrum.continuousOn _), cfc_id' (p := IsSelfAdjoint) ℝ M hM]
    _ = cfc (fun x => x * Real.log x) M + cfc (fun x => Real.log c * x) M := by
      rw [hscalar]
      exact cfc_add (p := IsSelfAdjoint) (a := M)
        (fun x : ℝ => x * Real.log x) (fun x => Real.log c * x)
        (M.finite_real_spectrum.continuousOn _) (M.finite_real_spectrum.continuousOn _)
    _ = M * matrixLog M + Real.log c • M := by
      rw [cfc_mul (fun x : ℝ => x) Real.log M (M.finite_real_spectrum.continuousOn _)
        (M.finite_real_spectrum.continuousOn _), cfc_id' (p := IsSelfAdjoint) ℝ M hM,
        cfc_const_mul_id (p := IsSelfAdjoint) _ M hM]
      rfl

open WildeQIT QAlgorithms

variable {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/- Generic partial-trace identities reused from checked SSA2_HSAlgebra.lean. -/
omit [Fintype A] [DecidableEq A] [DecidableEq B] in
lemma partialTrace_conjTranspose (Y : Matrix (A × B) (A × B) ℂ) :
    partialTraceRight Yᴴ = (partialTraceRight Y)ᴴ := by
  ext i j
  simp [partialTraceRight, Matrix.conjTranspose_apply]

omit [DecidableEq A] [DecidableEq B] in
lemma trace_partialTrace (Y : Matrix (A × B) (A × B) ℂ) :
    Matrix.trace (partialTraceRight Y) = Matrix.trace Y := by
  simp [partialTraceRight, Matrix.trace, Matrix.diag, Fintype.sum_prod_type]

omit [DecidableEq A] in
lemma partialTrace_mul_kronecker (Y : Matrix (A × B) (A × B) ℂ) (X : Matrix A A ℂ) :
    partialTraceRight (Y * (X ⊗ₖ (1 : Matrix B B ℂ))) = partialTraceRight Y * X := by
  ext i j
  simp [partialTraceRight, Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_mul,
    Matrix.one_apply]
  exact Finset.sum_comm

lemma weighted_log_trace [Nonempty B] (ρ : Matrix (A × B) (A × B) ℂ)
    (hρ : IsDensityMatrix ρ) :
    Matrix.trace (ρ * matrixLog (partialTraceRight ρ ⊗ₖ maximallyMixed B)) =
      Matrix.trace (partialTraceRight ρ * matrixLog (partialTraceRight ρ)) -
        (Real.log (Fintype.card B) : ℂ) := by
  have hM : (partialTraceRight ρ).IsHermitian := by
    change (partialTraceRight ρ)ᴴ = partialTraceRight ρ
    rw [← partialTrace_conjTranspose, hρ.1.1.eq]
  have hc : (Fintype.card B : ℝ)⁻¹ ≠ 0 := inv_ne_zero (by
    exact_mod_cast Fintype.card_ne_zero)
  have hscale : maximallyMixed B =
      (((Fintype.card B : ℝ)⁻¹ : ℝ) : ℂ) • (1 : Matrix B B ℂ) := by
    simp [maximallyMixed]
  rw [matrixLog, hscale, cfc_tensor_scalar _ hM,
    ← trace_partialTrace, partialTrace_mul_kronecker,
    weighted_log_mul _ hM _ hc, Matrix.trace_add, Matrix.trace_smul,
    trace_partialTrace, hρ.2, Real.log_inv]
  simp [Complex.real_smul, sub_eq_add_neg]

end
end SimpleSSA.Monotone.ConditionalProof

open SimpleSSA.Monotone TroppMatrixConcentration QAlgorithms WildeQIT

/-- Equation (5), including singular density matrices. -/
theorem solution {A B : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (ρ : Matrix (A × B) (A × B) ℂ) (hρ : IsDensityMatrix ρ) :
    entropy ρ - entropy (partialTraceRight ρ) =
      Real.log (Fintype.card B) - relEntropy ρ (partialTraceRight ρ ⊗ₖ maximallyMixed B) := by
  have h := ConditionalProof.weighted_log_trace ρ hρ
  unfold entropy relEntropy
  rw [Matrix.trace_sub, h, Complex.sub_re, Complex.sub_re, Complex.ofReal_re]
  ring
