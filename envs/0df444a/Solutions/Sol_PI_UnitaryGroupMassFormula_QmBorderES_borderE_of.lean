-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmBorderES.borderE_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:07:03.277746+00:00
-- url     : https://prove2.me/submissions/3f7f077f-0a42-42ec-90a8-1bcb65aac716

import Definitions.Def_Formalism_PeriodIntegrals_QmBorderES
import Definitions.Def_Formalism_PeriodIntegrals_QmColExp
import Definitions.Def_Formalism_PeriodIntegrals_QmRowExp
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderSignIdentity_SkipOneEqSuccAbove
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderES_Tm_of_ne
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderES_zmul
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderES_rowPart
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderES_comp_skip

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.QmBorderES
namespace PI.UnitaryGroupMassFormula.QmBorderES
theorem _root_.solution (hC : PI.ExpFirstCol) (hR : PI.ExpLastRow) : PI.BorderE := by
  intro A _ _ n m E e es v hG hB u
  obtain ⟨_, _, hve, _⟩ := hB
  rw [hC A n m E (PI.bE e v) (PI.bE e v) u, Fin.sum_univ_succ]
  have hsucc : PI.bE e v ∘ Fin.succ = v := by funext j; simp [PI.bE]
  have h0 : PI.bE e v 0 = e := by simp [PI.bE]
  simp only [Fin.succAbove_zero, hsucc, h0, Fin.val_zero, pow_zero, Int.cast_one, one_mul]
  rw [sub_eq_add_neg (Tm E u e e * qminor E v v (u - 1)), ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun w _ => ?_
  cases m with
  | zero => exact w.elim0
  | succ k =>
  have hrow : PI.bE e v ∘ (Fin.succ w).succAbove = PI.bE e (v ∘ w.succAbove) := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [PI.bE, Fin.succ_succAbove_zero]
    · simp [PI.bE, Fin.succ_succAbove_succ]
  have hvw : PI.bE e v w.succ = v w := by simp [PI.bE]
  rw [hrow, hvw, Tm_of_ne E u (hve w), rowPart hR E hG e (v ∘ w.succAbove) v hve (u - 1),
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  erw [comp_skip v w, comp_skip v x]
  rw [show u - 1 - 1 = u - 2 by ring]
  simp only [zmul, mul_smul_comm, smul_mul_assoc, smul_smul, Fin.val_succ, mul_assoc]
  rw [← neg_smul]
  congr 1
  ring
end PI.UnitaryGroupMassFormula.QmBorderES
