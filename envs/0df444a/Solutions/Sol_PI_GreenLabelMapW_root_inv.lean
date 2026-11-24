-- Prove2me | solution 1 for PI.GreenLabelMapW.root_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:01.363541+00:00
-- url     : https://prove2.me/submissions/e8da9ea4-f255-491a-b5ea-e3259a6339a2

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisConjCentralIdempotent
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelCharpoly_RootPowCard
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelCharpoly_IrreducibleCharpolyInv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES
noncomputable section
open PI PI.GreenLabelMapW
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
namespace PI.GreenLabelMapW
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (γ : GL ι K) {z : AlgebraicClosure K}
    (hz0 : z ≠ 0) (hz : aeval z (Matrix.charpoly (γ : Matrix ι ι K)) = 0) :
    aeval z⁻¹ (Matrix.charpoly ((γ⁻¹ : GL ι K) : Matrix ι ι K)) = 0 := by
  classical
  have key : ∀ (M : Matrix ι ι K) (w : AlgebraicClosure K),
      aeval w M.charpoly = (Matrix.scalar ι w - M.map (algebraMap K (AlgebraicClosure K))).det := by
    intro M w
    rw [← Polynomial.eval_map_algebraMap, ← Matrix.charpoly_map, Matrix.eval_charpoly]
  have hAB : ((γ⁻¹ : GL ι K) : Matrix ι ι K).map (algebraMap K (AlgebraicClosure K)) *
      (γ : Matrix ι ι K).map (algebraMap K (AlgebraicClosure K)) = 1 := by
    rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    simp
  rw [key] at hz ⊢
  have hs : ∀ w : AlgebraicClosure K, Matrix.scalar ι w = w • (1 : Matrix ι ι (AlgebraicClosure K)) := by
    intro w
    simp [Matrix.smul_one_eq_diagonal]
  have hmat : Matrix.scalar ι z⁻¹ - ((γ⁻¹ : GL ι K) : Matrix ι ι K).map (algebraMap K (AlgebraicClosure K)) =
      -(z⁻¹ • ((γ⁻¹ : GL ι K) : Matrix ι ι K).map (algebraMap K (AlgebraicClosure K))) *
        (Matrix.scalar ι z - (γ : Matrix ι ι K).map (algebraMap K (AlgebraicClosure K))) := by
    rw [hs, hs, neg_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul,
      inv_mul_cancel₀ hz0, one_smul, Matrix.smul_mul, hAB]
    abel
  rw [hmat, Matrix.det_mul, hz, mul_zero]
end PI.GreenLabelMapW
