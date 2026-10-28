-- Prove2me | solution 1 for SimpleSSA.Monotone.eq_7
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T07:16:41.181621+00:00
-- url     : https://prove2.me/submissions/aca0d49f-43a9-42e4-ab29-ba1ec70eaf55

import Mathlib
import Definitions.Def_SimpleSSA_Monotone_Basic

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder Kronecker
open Matrix TroppMatrixConcentration

namespace SimpleSSA.Monotone.ModularProof

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

theorem conj_diag_add {n : Type*} [Fintype n] [DecidableEq n]
    (U : unitary (Matrix n n ℂ)) (x y : n → ℝ) :
    ((U : Matrix n n ℂ) * diagonal (fun i => (x i : ℂ)) * star (U : Matrix n n ℂ)) +
      ((U : Matrix n n ℂ) * diagonal (fun i => (y i : ℂ)) * star (U : Matrix n n ℂ)) =
    (U : Matrix n n ℂ) * diagonal (fun i => ((x i + y i : ℝ) : ℂ)) *
      star (U : Matrix n n ℂ) := by
  simp only [← add_mul, ← mul_add, ← diagonal_add, Complex.ofReal_add]

theorem log_tensor_diag {n m : Type*} [Fintype n] [Fintype m]
    [DecidableEq n] [DecidableEq m]
    (U : unitary (Matrix n n ℂ)) (V : unitary (Matrix m m ℂ))
    (a : n → ℝ) (b : m → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j) :
    cfc Real.log
      (((U : Matrix n n ℂ) * diagonal (fun i => (a i : ℂ)) * star (U : Matrix n n ℂ)) ⊗ₖ
        ((V : Matrix m m ℂ) * diagonal (fun j => (b j : ℂ)) * star (V : Matrix m m ℂ))) =
    (((U : Matrix n n ℂ) * diagonal (fun i => (Real.log (a i) : ℂ)) *
        star (U : Matrix n n ℂ)) ⊗ₖ (1 : Matrix m m ℂ)) +
      ((1 : Matrix n n ℂ) ⊗ₖ ((V : Matrix m m ℂ) *
        diagonal (fun j => (Real.log (b j) : ℂ)) * star (V : Matrix m m ℂ))) := by
  have hu : (U : Matrix n n ℂ) * diagonal (fun _ => ((1 : ℝ) : ℂ)) *
      star (U : Matrix n n ℂ) = 1 := by simp
  have hv : (V : Matrix m m ℂ) * diagonal (fun _ => ((1 : ℝ) : ℂ)) *
      star (V : Matrix m m ℂ) = 1 := by simp
  have he1 := tensor_conj U V (fun i => Real.log (a i)) (fun _ => 1)
  have he2 := tensor_conj U V (fun _ => 1) (fun j => Real.log (b j))
  simp only [mul_one, hu, hv, one_mul] at he1 he2
  rw [← tensor_conj U V a b, cfc_diag_conj, ← he1, ← he2, conj_diag_add]
  congr 2
  apply congrArg diagonal
  funext i
  rw [Real.log_mul (ha i.1).ne' (hb i.2).ne']

set_option backward.isDefEq.respectTransparency false in
theorem log_kronecker {n m : Type*} [Fintype n] [Fintype m]
    [DecidableEq n] [DecidableEq m] (A : Matrix n n ℂ) (B : Matrix m m ℂ)
    (hA : A.PosDef) (hB : B.PosDef) :
    matrixLog (A ⊗ₖ B) = (matrixLog A ⊗ₖ (1 : Matrix m m ℂ)) +
      ((1 : Matrix n n ℂ) ⊗ₖ matrixLog B) := by
  have he := log_tensor_diag hA.1.eigenvectorUnitary hB.1.eigenvectorUnitary
    hA.1.eigenvalues hB.1.eigenvalues hA.eigenvalues_pos hB.eigenvalues_pos
  have ha := hA.1.spectral_theorem
  have hb := hB.1.spectral_theorem
  have hla := hA.1.cfc_eq Real.log
  have hlb := hB.1.cfc_eq Real.log
  simp only [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Function.comp_def,
    RCLike.ofReal_eq_complex_ofReal] at ha hb hla hlb
  simpa only [← ha, ← hb, ← hla, ← hlb, matrixLog] using he

set_option maxHeartbeats 1000000 in
theorem cfc_transpose {n : Type*} [Fintype n] [DecidableEq n] (H : Matrix (n) (n) ℂ)
    (hH : H.IsHermitian) (f : ℝ → ℝ) :
    cfc f H.transpose = (cfc f H).transpose := by
  let U := hH.eigenvectorUnitary
  let V := Matrix.UnitaryGroup.map_star U
  have ht (x : n → ℝ) :
      ((U : Matrix (n) (n) ℂ) * diagonal (fun i => (x i : ℂ)) * star (U : Matrix (n) (n) ℂ)).transpose =
        (V : Matrix (n) (n) ℂ) * diagonal (fun i => (x i : ℂ)) * star (V : Matrix (n) (n) ℂ) := by
    simp only [transpose_mul, diagonal_transpose, star_eq_conjTranspose]
    rw [Matrix.mul_assoc]
    congr 2
    change (U : Matrix (n) (n) ℂ).transpose = ((U : Matrix (n) (n) ℂ).map star).conjTranspose
    ext i j
    simp
  have hs := hH.spectral_theorem
  simp only [Unitary.conjStarAlgAut_apply, Function.comp_def, RCLike.ofReal_eq_complex_ofReal] at hs
  rw [hs, ht, cfc_diag_conj, cfc_diag_conj, ht]


set_option backward.isDefEq.respectTransparency false in
theorem log_inv {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.PosDef) : matrixLog A⁻¹ = -matrixLog A := by
  have hi : cfc (fun x : ℝ => x⁻¹) A = A⁻¹ := by
    rw [cfc_ringInverse_id (R := ℝ) (p := IsSelfAdjoint) A hA.isUnit hA.1, Matrix.nonsing_inv_eq_ringInverse]
  change cfc Real.log A⁻¹ = -cfc Real.log A
  rw [← hi, ← cfc_comp' (p := IsSelfAdjoint) Real.log (fun x : ℝ => x⁻¹) A
    ((A.finite_real_spectrum.image _).continuousOn _)
    (A.finite_real_spectrum.continuousOn _) hA.1]
  simp only [Real.log_inv, cfc_neg]

theorem log_modularOp {n : Type} [Fintype n] [DecidableEq n]
    (ρ σ : Matrix n n ℂ) (hρ : ρ.PosDef) (hσ : σ.PosDef) :
    matrixLog (modularOp ρ σ) =
      (matrixLog σ ⊗ₖ (1 : Matrix n n ℂ)) -
        ((1 : Matrix n n ℂ) ⊗ₖ (matrixLog ρ).transpose) := by
  rw [modularOp, log_kronecker σ (ρ⁻¹).transpose hσ hρ.inv.transpose]
  have ht : matrixLog (ρ⁻¹).transpose = (matrixLog ρ⁻¹).transpose :=
    cfc_transpose _ hρ.inv.1 Real.log
  rw [ht, log_inv ρ hρ, transpose_neg]
  ext i j
  simp [Matrix.kroneckerMap, sub_eq_add_neg]

end
end SimpleSSA.Monotone.ModularProof

namespace SimpleSSA.Monotone.Eq7SpectralProof

variable {A : Type} [Fintype A] [DecidableEq A]
variable {M : Matrix A A ℂ}

lemma sqrtM_isHermitian (M : Matrix A A ℂ) : (sqrtM M).IsHermitian :=
  cfc_predicate Real.sqrt M

lemma invSqrtM_isHermitian (M : Matrix A A ℂ) : (invSqrtM M).IsHermitian :=
  cfc_predicate (fun x : ℝ => (Real.sqrt x)⁻¹) M

lemma sqrtM_conjTranspose (M : Matrix A A ℂ) : (sqrtM M)ᴴ = sqrtM M :=
  sqrtM_isHermitian M

lemma invSqrtM_conjTranspose (M : Matrix A A ℂ) : (invSqrtM M)ᴴ = invSqrtM M :=
  invSqrtM_isHermitian M

lemma sqrtM_mul_self (hM : M.PosSemidef) : sqrtM M * sqrtM M = M := by
  change cfc Real.sqrt M * cfc Real.sqrt M = M
  rw [← cfc_mul Real.sqrt Real.sqrt M]
  calc
    cfc (fun x => Real.sqrt x * Real.sqrt x) M = cfc (fun x : ℝ => x) M :=
      cfc_congr (fun x hx => Real.mul_self_sqrt (spectrum_nonneg_of_nonneg hM.nonneg hx))
    _ = M := cfc_id' ℝ M hM.isHermitian

lemma spectrum_pos (hM : M.PosDef) {x : ℝ} (hx : x ∈ spectrum ℝ M) : 0 < x :=
  hM.isStrictlyPositive.spectrum_pos hx

lemma sqrtM_mul_invSqrtM (hM : M.PosDef) : sqrtM M * invSqrtM M = 1 := by
  exact (cfcUnits Real.sqrt M
    (fun x hx => ne_of_gt (Real.sqrt_pos.2 (spectrum_pos hM hx)))
    (ha := hM.isHermitian)).val_inv

lemma invSqrtM_mul_sqrtM (hM : M.PosDef) : invSqrtM M * sqrtM M = 1 := by
  exact (cfcUnits Real.sqrt M
    (fun x hx => ne_of_gt (Real.sqrt_pos.2 (spectrum_pos hM hx)))
    (ha := hM.isHermitian)).inv_val

lemma sqrtM_inv (hM : M.PosDef) : (sqrtM M)⁻¹ = invSqrtM M :=
  Matrix.inv_eq_right_inv (sqrtM_mul_invSqrtM hM)

lemma invSqrtM_mul_self (hM : M.PosDef) : invSqrtM M * invSqrtM M = M⁻¹ := by
  rw [← sqrtM_inv hM, ← Matrix.mul_inv_rev, sqrtM_mul_self hM.posSemidef]

lemma invSqrtM_mul_self_mul_invSqrtM (hM : M.PosDef) :
    invSqrtM M * M * invSqrtM M = 1 := by
  calc
    invSqrtM M * M * invSqrtM M =
        invSqrtM M * (sqrtM M * sqrtM M) * invSqrtM M := by
      rw [sqrtM_mul_self hM.posSemidef]
    _ = (invSqrtM M * sqrtM M) * (sqrtM M * invSqrtM M) := by
      simp only [Matrix.mul_assoc]
    _ = 1 := by rw [invSqrtM_mul_sqrtM hM, sqrtM_mul_invSqrtM hM, one_mul]

lemma sqrtM_mul_inv_mul_sqrtM (hM : M.PosDef) :
    sqrtM M * M⁻¹ * sqrtM M = 1 := by
  rw [← invSqrtM_mul_self hM, ← Matrix.mul_assoc, sqrtM_mul_invSqrtM hM,
    one_mul, invSqrtM_mul_sqrtM hM]

end SimpleSSA.Monotone.Eq7SpectralProof

namespace SimpleSSA.Monotone.ModularProof

variable {A : Type} [Fintype A] [DecidableEq A]

omit [DecidableEq A] in
lemma applyHS_kronecker (B C X : Matrix A A ℂ) :
    applyHS (B ⊗ₖ C.transpose) X = B * X * C := by
  ext i j
  have h := congrFun (Matrix.kronecker_mulVec_vec C.transpose X.transpose B) (i, j)
  have hv : X.transpose.vec = vecHS X := rfl
  rw [hv] at h
  change ((B ⊗ₖ C.transpose) *ᵥ vecHS X) (i, j) = (B * X * C) i j
  simpa only [← Matrix.transpose_mul, Matrix.transpose_apply, Matrix.vec, vecHS, Matrix.mul_assoc] using h

lemma applyHS_left (B X : Matrix A A ℂ) :
    applyHS (B ⊗ₖ (1 : Matrix A A ℂ)) X = B * X := by
  simpa only [transpose_one, mul_one] using applyHS_kronecker B 1 X

lemma applyHS_right (C X : Matrix A A ℂ) :
    applyHS ((1 : Matrix A A ℂ) ⊗ₖ C.transpose) X = X * C := by
  simpa only [one_mul] using applyHS_kronecker 1 C X

omit [DecidableEq A] in
lemma applyHS_sub (B C : Matrix (A × A) (A × A) ℂ) (X : Matrix A A ℂ) :
    applyHS (B - C) X = applyHS B X - applyHS C X := by
  ext i j
  simp [applyHS, Matrix.sub_mulVec]

lemma neg_log_modular_action (ρ σ X : Matrix A A ℂ) (hρ : ρ.PosDef) (hσ : σ.PosDef) :
    applyHS (-(matrixLog (modularOp ρ σ))) X = X * matrixLog ρ - matrixLog σ * X := by
  rw [log_modularOp ρ σ hρ hσ, neg_sub, applyHS_sub, applyHS_right, applyHS_left]

omit [DecidableEq A] in
lemma trace_mul_hermitian_real (B C : Matrix A A ℂ)
    (hB : B.IsHermitian) (hC : C.IsHermitian) :
    ((Matrix.trace (B * C)).re : ℂ) = Matrix.trace (B * C) := by
  apply Complex.conj_eq_iff_re.mp
  change star (Matrix.trace (B * C)) = Matrix.trace (B * C)
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hB.eq, hC.eq,
    Matrix.trace_mul_comm]

lemma relative_entropy_complex (ρ σ : Matrix A A ℂ) (hρ : ρ.IsHermitian) :
    (relEntropy ρ σ : ℂ) = Matrix.trace (ρ * matrixLog ρ - ρ * matrixLog σ) := by
  have hlogρ : (matrixLog ρ).IsHermitian := cfc_predicate Real.log ρ
  have hlogσ : (matrixLog σ).IsHermitian := cfc_predicate Real.log σ
  unfold relEntropy
  rw [Matrix.trace_sub, Complex.sub_re, Complex.ofReal_sub,
    trace_mul_hermitian_real ρ (matrixLog ρ) hρ hlogρ,
    trace_mul_hermitian_real ρ (matrixLog σ) hρ hlogσ]

lemma eq7_of_posDef (ρ σ : Matrix A A ℂ) (hρ : ρ.PosDef) (hσ : σ.PosDef) :
    (relEntropy ρ σ : ℂ) =
      hsInner (sqrtM ρ) (applyHS (-(matrixLog (modularOp ρ σ))) (sqrtM ρ)) := by
  rw [relative_entropy_complex ρ σ hρ.1, neg_log_modular_action ρ σ (sqrtM ρ) hρ hσ,
    hsInner, Eq7SpectralProof.sqrtM_conjTranspose]
  rw [mul_sub, ← Matrix.mul_assoc, Eq7SpectralProof.sqrtM_mul_self hρ.posSemidef,
    Matrix.trace_sub, Matrix.trace_sub]
  congr 1
  rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle, Eq7SpectralProof.sqrtM_mul_self hρ.posSemidef]

end SimpleSSA.Monotone.ModularProof

open SimpleSSA.Monotone QAlgorithms

/-- Nielsen–Petz equation (7): the relative modular operator expression for relative entropy. -/
theorem solution {A : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    (ρ σ : Matrix A A ℂ) (hρ : IsDensityMatrix ρ) (hρ_inv : ρ.PosDef)
    (hσ : IsDensityMatrix σ) (hσ_inv : σ.PosDef) :
    (relEntropy ρ σ : ℂ) =
      hsInner (sqrtM ρ) (applyHS (-(matrixLog (modularOp ρ σ))) (sqrtM ρ)) := by
  exact ModularProof.eq7_of_posDef ρ σ ⟨hρ.1.1, hρ_inv.2⟩ ⟨hσ.1.1, hσ_inv.2⟩
