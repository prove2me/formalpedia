-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P41.operatorSumRepresentation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T00:10:33.549992+00:00
-- url     : https://prove2.me/submissions/2f980ff8-84b1-4fcb-9dfd-a54d6aeab7ba

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P41

-- ===== P41CKLib =====

noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P41
open QAlgorithms.Entanglement (IsCompletelyPositive)
open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq
local instance (priority := 2000) (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

namespace X4P41C
open Matrix

variable {d : ℕ}

/-- unnormalized maximally entangled projector on (Fin d × Fin d) -/
def omega (d : ℕ) : Fin d × Fin d → ℂ := fun p => if p.1 = p.2 then 1 else 0

lemma choi_psd (Phi : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (hCP : IsCompletelyPositive Phi) :
    (idTensorSuperop Phi (vecMulVec (omega d) (star (omega d)))).PosSemidef :=
  hCP d _ (posSemidef_vecMulVec_self_star _)

lemma choi_entry (Phi : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (i a j b : Fin d) :
    idTensorSuperop Phi (vecMulVec (omega d) (star (omega d))) (i, a) (j, b) =
      Phi (Matrix.single i j 1) a b := by
  simp only [idTensorSuperop, Matrix.of_apply]
  have h : (Matrix.of fun x y => vecMulVec (omega d) (star (omega d)) (i, x) (j, y)) =
      Matrix.single i j (1 : ℂ) := by
    ext x y
    simp only [Matrix.of_apply, vecMulVec_apply, omega, Pi.star_apply, Matrix.single_apply]
    by_cases h1 : i = x <;> by_cases h2 : j = y <;> simp [h1, h2]
  rw [h]

theorem kraus_exists (Phi : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (hCP : IsCompletelyPositive Phi) :
    ∃ A : Fin d × Fin d → Matrix (Fin d) (Fin d) ℂ, ∀ X, Phi X = ∑ k, A k * X * (A k)ᴴ := by
  set C := idTensorSuperop Phi (vecMulVec (omega d) (star (omega d)))
  have hC : C.PosSemidef := choi_psd Phi hCP
  set U := hC.1.eigenvectorUnitary
  set lam := hC.1.eigenvalues
  have hspec := hC.1.spectral_theorem
  have hentry : ∀ p q, C p q = ∑ k, (U : Matrix _ _ ℂ) p k * (lam k : ℂ) * conj ((U : Matrix _ _ ℂ) q k) := by
    intro p q
    have := congrFun (congrFun hspec p) q
    rw [this]
    simp only [Unitary.conjStarAlgAut_apply, Matrix.mul_apply, diagonal_apply, Function.comp_apply,
      star_apply, RCLike.star_def, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rfl
  have hentry' : ∀ i a j b, Phi (Matrix.single i j 1) a b =
      ∑ k, (U : Matrix _ _ ℂ) (i, a) k * (lam k : ℂ) * conj ((U : Matrix _ _ ℂ) (j, b) k) := by
    intro i a j b
    rw [← choi_entry Phi i a j b]
    exact hentry (i, a) (j, b)
  refine ⟨fun k => Matrix.of fun a i => ((Real.sqrt (lam k) : ℝ) : ℂ) * (U : Matrix _ _ ℂ) (i, a) k, ?_⟩
  intro X
  have hX : X = ∑ i, ∑ j, X i j • Matrix.single i j (1 : ℂ) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single X]
    simp [Matrix.smul_single]
  ext a b
  conv_lhs => rw [hX]
  simp only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    conjTranspose_apply, RCLike.star_def, map_mul, Complex.conj_ofReal, Matrix.of_apply]
  simp_rw [hentry']
  simp only [Finset.mul_sum, Finset.sum_mul]
  have perm : ∀ f : Fin d → Fin d → Fin d × Fin d → ℂ,
      (∑ i, ∑ j, ∑ k, f i j k) = ∑ k, ∑ j, ∑ i, f i j k := by
    intro f
    rw [Finset.sum_congr rfl (fun i _ => (Finset.sum_comm : (∑ j, ∑ k, f i j k) = _))]
    rw [(Finset.sum_comm : (∑ i, ∑ k, ∑ j, f i j k) = _)]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_comm
  rw [perm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun i _ => ?_
  have hl : 0 ≤ lam k := hC.eigenvalues_nonneg k
  have : ((Real.sqrt (lam k) : ℝ) : ℂ) * ((Real.sqrt (lam k) : ℝ) : ℂ) = (lam k : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hl]
  linear_combination (X i j * (U : Matrix _ _ ℂ) (i, a) k * conj ((U : Matrix _ _ ℂ) (j, b) k)) * this.symm

end X4P41C

-- ===== P41OS =====

noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P41
open QAlgorithms.Entanglement (IsCompletelyPositive)
open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq
local instance (priority := 2000) (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

namespace X4P41O
open Matrix

lemma tp_kraus {d m : ℕ} (A : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (hTP : ∀ X, (krausApply A X).trace = X.trace) : IsKrausFamily A := by
  unfold IsKrausFamily
  set M := ∑ k, (A k)ᴴ * A k
  have hM : ∀ X, (M * X).trace = X.trace := by
    intro X
    rw [← hTP X, krausApply, Matrix.trace_sum, Matrix.sum_mul, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.trace_mul_comm (X * (A k)ᴴ) (A k),
      ← Matrix.mul_assoc]
  ext i j
  have := hM (Matrix.single j i 1)
  rw [Matrix.trace_mul_single] at this
  have ht : (Matrix.single j i (1 : ℂ)).trace = if i = j then 1 else 0 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.single_apply]
    by_cases h : i = j
    · subst h; simp
    · simp [h, Ne.symm h]
  rw [ht] at this
  simp only [one_apply]
  simpa using this

end X4P41O

theorem solution {d : ℕ} [NeZero d]
    (Phi : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (hCP : IsCompletelyPositive Phi) (hTP : ∀ X, (Phi X).trace = X.trace) :
    ∃ m : ℕ, m ≤ d^2 ∧ ∃ A : Fin m → Matrix (Fin d) (Fin d) ℂ,
      OperatorSum Phi A := by
  obtain ⟨A, hA⟩ := X4P41C.kraus_exists Phi hCP
  let e : Fin d × Fin d ≃ Fin (d^2) := finProdFinEquiv.trans (finCongr (by ring))
  have hk : ∀ X, Phi X = krausApply (fun k => A (e.symm k)) X := by
    intro X
    rw [hA X, krausApply]
    exact (e.symm.sum_comp (fun k => A k * X * (A k)ᴴ)).symm
  refine ⟨d^2, le_rfl, fun k => A (e.symm k), X4P41O.tp_kraus _ fun X => ?_, hk⟩
  rw [← hk X, hTP]

#print axioms solution
