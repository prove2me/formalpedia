-- Prove2me | solution 1 for UpperTheory.Reformulated.B.MirabolicColumnBlock.conj_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:57:48.47067+00:00
-- url     : https://prove2.me/submissions/7b50d347-e6b7-4672-8510-8f5812d456ee

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MirabolicColumnBlock

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory UpperTheory.Reformulated UpperTheory.Reformulated.B UpperTheory.Reformulated.B.MirabolicColumnBlock
namespace UpperTheory.Reformulated.B.MirabolicColumnBlock
theorem _root_.solution {K : Type} [Field K] {n : ℕ} (d : Fin n → K) (hd : Function.Injective d)
    (M : Matrix (Fin n) (Fin n) K) (hM : M.charpoly = ∏ a, (Polynomial.X - Polynomial.C (d a))) :
    ∃ h : GL (Fin n) K, ((h⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * M * h = Matrix.diagonal d := by
  have hev : ∀ a, ∃ v : Fin n → K, Module.End.HasEigenvector (Matrix.toLin' M) (d a) v := by
    intro a
    apply Module.End.HasEigenvalue.exists_hasEigenvector
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin', hM,
      Polynomial.IsRoot.def, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ a) (by simp)
  choose v hv using hev
  have hli : LinearIndependent K v :=
    Module.End.eigenvectors_linearIndependent' (Matrix.toLin' M) d hd v hv
  have hu : IsUnit (Matrix.of v).transpose := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    exact hli
  have hmul : M * (Matrix.of v).transpose = (Matrix.of v).transpose * Matrix.diagonal d := by
    ext i a
    have h := congrFun (hv a).apply_eq_smul i
    rw [Matrix.toLin'_apply] at h
    rw [Matrix.mul_diagonal, mul_comm]
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using h
  obtain ⟨u, hu⟩ := hu
  refine ⟨u, ?_⟩
  rw [Matrix.mul_assoc, hu, hmul, ← hu, ← Matrix.mul_assoc]
  simp
end UpperTheory.Reformulated.B.MirabolicColumnBlock
