-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmBorderES.borderS_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:10:50.672947+00:00
-- url     : https://prove2.me/submissions/e3d0e754-a7c1-473a-9e10-4d22c8de8174

import Definitions.Def_Formalism_PeriodIntegrals_QmBorderES
import Definitions.Def_Formalism_PeriodIntegrals_QmColExp
import Definitions.Def_Formalism_PeriodIntegrals_QmRowExp
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderSignIdentity_SkipOneEqSuccAbove
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderES_neg_one_pow_mul_self
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderES_Tm_of_ne
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderES_zmul
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderES_colPart
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
theorem _root_.solution (hC : PI.ExpLastCol) (hF : PI.ExpFirstRow) : PI.BorderS := by
  intro A _ _ n m E e es v hG hB u
  obtain ⟨_, _, _, hves⟩ := hB
  rw [hC A n m E (PI.bS v es) (PI.bS v es) u, Fin.sum_univ_castSucc]
  have hcs : PI.bS v es ∘ Fin.castSucc = v := by funext j; simp [PI.bS]
  have hl : PI.bS v es (Fin.last m) = es := by simp [PI.bS]
  simp only [Fin.succAbove_last, hcs, hl, Fin.val_last]
  rw [pow_add, neg_one_pow_mul_self, Int.cast_one, one_mul, add_comm,
    sub_eq_add_neg (qminor E v v u * Tm E (u - (m : ℂ)) es es), ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun w _ => ?_
  cases m with
  | zero => exact w.elim0
  | succ k =>
  have hrow : PI.bS v es ∘ (Fin.castSucc w).succAbove = PI.bS (v ∘ w.succAbove) es := by
    funext j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · have : (Fin.castSucc w).succAbove (Fin.last k) = Fin.last (k + 1) := by
        rw [Fin.succAbove_of_le_castSucc _ _ (by simpa using Fin.le_last w), Fin.succ_last]
      simp [PI.bS, this]
    · simp [PI.bS, Fin.castSucc_succAbove_castSucc]
  have hvw : PI.bS v es (Fin.castSucc w) = v w := by simp [PI.bS]
  rw [hrow, hvw, Tm_of_ne E (u - ((k + 1 : ℕ) : ℂ)) (hves w), colPart hF E hG es (v ∘ w.succAbove) v hves u,
    Finset.sum_mul, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  erw [comp_skip v w, comp_skip v x]
  simp only [zmul, mul_smul_comm, smul_mul_assoc, smul_smul, Fin.coe_castSucc, mul_assoc]
  rw [← neg_smul]
  congr 1
  linear_combination (-(-1 : ℤ) ^ ((w : ℕ) + (x : ℕ))) * neg_one_pow_mul_self k
end PI.UnitaryGroupMassFormula.QmBorderES
