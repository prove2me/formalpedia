-- Prove2me | solution 1 for PI.OddDualWeyl.Jac.jacobi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:06:10.739787+00:00
-- url     : https://prove2.me/submissions/ecf0131b-7635-4909-b0bb-b9406d9dfb6c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacobiMinorIdentity
import Theorems.Thm_PI_OddDualWeyl_Jac_block
import Theorems.Thm_PI_OddDualWeyl_Jac_det_sub
import Theorems.Thm_PI_OddDualWeyl_Jac_sign_sq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MvPolynomial Matrix
noncomputable section
namespace PI.OddDualWeyl.Jac
private theorem mapMatrix_eval_generic_eq {R : Type*} [CommRing R] {k : ℕ} (A : Matrix (Fin k) (Fin k) R) :
    (MvPolynomial.eval₂Hom (Int.castRingHom R) fun p : Fin k × Fin k => A p.1 p.2).mapMatrix
      (Matrix.of fun i j => (X (i, j) : MvPolynomial (Fin k × Fin k) ℤ)) = A := by
  ext i j
  simp
private theorem det_generic_int_ne_zero (k : ℕ) :
    (Matrix.of fun i j => (X (i, j) : MvPolynomial (Fin k × Fin k) ℤ)).det ≠ 0 := by
  intro h
  have h1 := congrArg
    (MvPolynomial.eval₂Hom (Int.castRingHom ℤ)
      fun p : Fin k × Fin k => (1 : Matrix (Fin k) (Fin k) ℤ) p.1 p.2) h
  rw [RingHom.map_det, mapMatrix_eval_generic_eq (1 : Matrix (Fin k) (Fin k) ℤ), det_one, map_zero] at h1
  exact one_ne_zero h1
private theorem det_toBlocks22_adjugate_submatrix_of_det_ne_zero {R : Type*} [CommRing R] [IsDomain R]
    {k : ℕ} {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [Nonempty n]
    (eI eJ : m ⊕ n ≃ Fin k) (A : Matrix (Fin k) (Fin k) R) (hA : A.det ≠ 0) :
    ((adjugate A).submatrix eJ eI).toBlocks₂₂.det =
      ((Equiv.Perm.sign (eJ.trans eI.symm) : ℤ) : R) * A.det ^ (Fintype.card n - 1) *
        (A.submatrix eI eJ).toBlocks₁₁.det := by
  have hBA : (adjugate A).submatrix eJ eI * A.submatrix eI eJ =
      A.det • (1 : Matrix (m ⊕ n) (m ⊕ n) R) := by
    rw [submatrix_mul_equiv, adjugate_mul]
    ext i j
    simp [Matrix.one_apply]
  have key := block (A.submatrix eI eJ) ((adjugate A).submatrix eJ eI) A.det hBA
  rw [det_sub] at key
  have hs2 := sign_sq (R := R) (Equiv.Perm.sign (eJ.trans eI.symm))
  have hpow : A.det ^ Fintype.card n = A.det * A.det ^ (Fintype.card n - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel (Fintype.card_pos (α := n))]
  have h2 : A.det * (((adjugate A).submatrix eJ eI).toBlocks₂₂.det *
      ((Equiv.Perm.sign (eJ.trans eI.symm) : ℤ) : R)) =
      A.det * (A.det ^ (Fintype.card n - 1) * (A.submatrix eI eJ).toBlocks₁₁.det) := by
    linear_combination key + (A.submatrix eI eJ).toBlocks₁₁.det * hpow
  have h3 := mul_left_cancel₀ hA h2
  linear_combination ((Equiv.Perm.sign (eJ.trans eI.symm) : ℤ) : R) * h3 -
    ((adjugate A).submatrix eJ eI).toBlocks₂₂.det * hs2
end PI.OddDualWeyl.Jac
namespace PI.OddDualWeyl.Jac
end PI.OddDualWeyl.Jac
namespace PI.OddDualWeyl
end PI.OddDualWeyl
end
end

set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.OddDualWeyl PI.OddDualWeyl.Jac
namespace PI.OddDualWeyl.Jac
theorem _root_.solution {R : Type*} [CommRing R] {k : ℕ} {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] [Nonempty n] (eI eJ : m ⊕ n ≃ Fin k)
    (A : Matrix (Fin k) (Fin k) R) :
    ((adjugate A).submatrix eJ eI).toBlocks₂₂.det =
      ((Equiv.Perm.sign (eJ.trans eI.symm) : ℤ) : R) * A.det ^ (Fintype.card n - 1) *
        (A.submatrix eI eJ).toBlocks₁₁.det := by
  obtain ⟨G, hG0, φ, hφG⟩ : ∃ G : Matrix (Fin k) (Fin k) (MvPolynomial (Fin k × Fin k) ℤ),
      G.det ≠ 0 ∧ ∃ φ : MvPolynomial (Fin k × Fin k) ℤ →+* R, φ.mapMatrix G = A :=
    ⟨_, det_generic_int_ne_zero k, _, mapMatrix_eval_generic_eq A⟩
  have hcore := det_toBlocks22_adjugate_submatrix_of_det_ne_zero eI eJ G hG0
  have hadj : φ.mapMatrix (adjugate G) = adjugate A := by
    rw [RingHom.map_adjugate, hφG]
  have e1 : φ.mapMatrix (((adjugate G).submatrix eJ eI).toBlocks₂₂) =
      ((adjugate A).submatrix eJ eI).toBlocks₂₂ := by
    ext i j
    exact congrFun (congrFun hadj (eJ (Sum.inr i))) (eI (Sum.inr j))
  have e2 : φ.mapMatrix ((G.submatrix eI eJ).toBlocks₁₁) = (A.submatrix eI eJ).toBlocks₁₁ := by
    ext i j
    exact congrFun (congrFun hφG (eI (Sum.inl i))) (eJ (Sum.inl j))
  have h := congrArg φ hcore
  simp only [map_mul, map_pow, map_intCast, RingHom.map_det, hφG, e1, e2] at h
  exact h
end PI.OddDualWeyl.Jac
