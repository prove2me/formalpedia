-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.CntFormula.UG.linIndep_orth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:38:27.597887+00:00
-- url     : https://prove2.me/submissions/fe9d7432-8305-4b5d-b4df-1dbcde7014a7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountingFormula_ExistsIsomMove
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsOrthogonalUnitVector
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountingFormula_ExistsIsomSelfDual
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CntFormula PI.UnitaryGroupMassFormula.CntFormula.UG
open Formalism.HermitianLattices.Ext.L3.WA
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {h : V →ₗ⋆[K] V →ₗ[K] K}
namespace PI.UnitaryGroupMassFormula.CntFormula.UG
theorem _root_.solution {ι : Type} [Fintype ι] (x : ι → V) (hxo : ∀ i j, i ≠ j → h (x i) (x j) = 0)
    (hx0 : ∀ i, h (x i) (x i) ≠ 0) : LinearIndependent K x := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have := congrArg (h (x j)) hc
  rw [map_sum, map_zero, Finset.sum_eq_single j] at this
  · rw [map_smul, smul_eq_mul] at this
    exact (mul_eq_zero.1 this).resolve_right (hx0 j)
  · intro i _ hij
    rw [map_smul, hxo j i (Ne.symm hij), smul_zero]
  · simp
end PI.UnitaryGroupMassFormula.CntFormula.UG
