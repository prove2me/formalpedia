-- Prove2me | solution 1 for PI.GGMatBoundW.matrix_coefficient_equation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:34:37.706976+00:00
-- url     : https://prove2.me/submissions/a05afbc3-c1cc-4977-ad20-f6b5416e920a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_PermRepApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_GammaMatrixInverse
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_MatrixCoefficientEquation
import Theorems.Thm_PI_GGMatBoundW_eq_of_smul_eq_of_free
import Theorems.Thm_PI_GGMatBoundW_exists_smul_comm
import Theorems.Thm_PI_GGMatBoundW_sum_orbit
import Theorems.Thm_PI_GGMatBoundW_gamProd_inv
import Theorems.Thm_P2M_PI_GGMatBoundW_toMatrix__totOp_apply_817037fb5a4c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
open scoped ComplexConjugate
noncomputable section
open Classical
open PI PI.GGMatBoundW
open Formalism.L2.SG.GGMirabolic
namespace PI.GGMatBoundW
theorem _root_.solution : MatrixEq := by
  intro ι _ Fq _ _ k ψ X _ _ hfree d hd
  constructor
  · ext i j
    rw [Matrix.of_apply, toMatrix'_totOp_apply, sum_orbit hfree d hd,
      exists_smul_comm (G := ∀ v, GL (Fin k) (Fq v)) i j]
    split_ifs with h
    · have h1 := hd j i h
      have h3 := hd i j ((exists_smul_comm (G := ∀ v, GL (Fin k) (Fq v)) i j).mpr h)
      have hdd : d j i = (d i j)⁻¹ := by
        apply MulOpposite.op_injective
        apply eq_of_smul_eq_of_free hfree (j := i)
        rw [h1, MulOpposite.op_inv]
        exact eq_inv_smul_iff.mpr h3
      rw [hdd, gamProd_inv]
    · rfl
  · ext i j
    rw [Matrix.of_apply, Matrix.transpose_apply, toMatrix'_totOp_apply, sum_orbit hfree d hd]
end PI.GGMatBoundW
