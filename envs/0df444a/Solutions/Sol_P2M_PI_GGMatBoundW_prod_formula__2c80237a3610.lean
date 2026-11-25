-- Prove2me | solution 1 for P2M_PI_GGMatBoundW_prod_formula__2c80237a3610
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:56:04.187158+00:00
-- url     : https://prove2.me/submissions/ae3ba5b8-1f70-401a-bbb1-67998779e4eb

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_PermRepApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_ProdFormula
import Theorems.Thm_PI_GGMatBoundW_beta_univ
import Theorems.Thm_PI_GGMatBoundW_totOp_apply
import Theorems.Thm_PI_GGMatBoundW_sum_beta_empty
import Theorems.Thm_PI_GGMatBoundW_sum_beta_insert

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Classical
open PI PI.GGMatBoundW
open Formalism.L2.SG.GGMirabolic
namespace PI.GGMatBoundW
theorem _root_.solution : ProdFormula := by
  intro ι _ Fq _ _ k ψ V _ _ π μ w hμ
  have key : ∀ s : Finset ι, ∑ x, beta ψ s x • π x w = (∏ v ∈ s, μ v) • w := by
    intro s
    induction s using Finset.induction_on with
    | empty => rw [sum_beta_empty, Finset.prod_empty, one_smul]
    | @insert a s ha ih =>
      rw [sum_beta_insert ψ π ha w, ih, map_smul, hμ, smul_smul, Finset.prod_insert ha, mul_comm]
  rw [totOp_apply, ← key Finset.univ]
  simp_rw [beta_univ]
end PI.GGMatBoundW
