-- Prove2me | solution 1 for PI.GGMatBoundW.totally_hermitian_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:35:11.456306+00:00
-- url     : https://prove2.me/submissions/2b92424c-b061-46e1-ba48-3d5b52ccfeea

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_PermRepApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_GammaMatrixInverse
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_MatrixCoefficientEquation
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
theorem _root_.solution : TotHerm := by
  intro ι _ Fq _ _ k ψ X _ _
  refine Matrix.IsHermitian.ext fun i j => ?_
  rw [toMatrix'_totOp_apply, toMatrix'_totOp_apply, star_sum]
  refine Fintype.sum_equiv (Equiv.inv _) _ _ fun x => ?_
  have hiff : MulOpposite.op x • j = i ↔ MulOpposite.op x⁻¹ • i = j := by
    rw [MulOpposite.op_inv]
    constructor
    · intro h
      rw [← h, inv_smul_smul]
    · intro h
      rw [← h, smul_inv_smul]
  simp only [Equiv.inv_apply]
  split_ifs with h1 h2 h2
  · rw [gamProd_inv]
    rfl
  · exact absurd (hiff.mp h1) h2
  · exact absurd (hiff.mpr h2) h1
  · exact star_zero _
end PI.GGMatBoundW
