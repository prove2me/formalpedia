-- Prove2me | solution 1 for PI.WHw.det_one_add_single_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:00:30.363946+00:00
-- url     : https://prove2.me/submissions/fda521dc-34c5-441a-9e9f-6845b5dbd555

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightIrreducible_ClosedEqNablaC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightIrreducible_ConstructionA
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.WHw
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
namespace PI.WHw
theorem _root_.solution {N : ℕ} (a b : Fin N) (n : ℕ) :
    (1 + Matrix.single a b (n : ℂ)).det ≠ 0 := by
  by_cases h : a = b
  · subst h
    have hd : (1 + Matrix.single a a (n : ℂ)) = Matrix.diagonal (fun i => if i = a then 1 + (n : ℂ) else 1) := by
      ext i j
      simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, Matrix.diagonal_apply, ite_and]
      split_ifs <;> subst_vars <;> simp_all
    rw [hd, Matrix.det_diagonal, Finset.prod_ite_eq', if_pos (Finset.mem_univ a)]
    have h1 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    rwa [add_comm] at h1
  · rw [show (1 + Matrix.single a b (n : ℂ)) = Matrix.transvection a b (n : ℂ) from rfl,
      Matrix.det_transvection_of_ne a b h]
    exact one_ne_zero
end PI.WHw
