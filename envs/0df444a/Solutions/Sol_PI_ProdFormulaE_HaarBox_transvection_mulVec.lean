-- Prove2me | solution 1 for PI.ProdFormulaE.HaarBox.transvection_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:05:49.905092+00:00
-- url     : https://prove2.me/submissions/84bc73f5-7de0-4571-9cb5-3ec086dbf6fd

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_HaarBox
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_HaarTransv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Module Matrix
open PI PI.ProdFormulaE PI.ProdFormulaE.HaarBox
variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {E : Type} [AddCommGroup E] [Module K E] [TopologicalSpace E] [IsModuleTopology K E]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace PI.ProdFormulaE.HaarBox
theorem _root_.solution (t : Matrix.TransvectionStruct ι K) (v : ι → K) (k : ι) :
    (t.toMatrix *ᵥ v) k = v k + if k = t.i then t.c * v t.j else 0 := by
  simp only [Matrix.TransvectionStruct.toMatrix, Matrix.transvection, Matrix.add_mulVec,
    Matrix.one_mulVec, Pi.add_apply, add_right_inj]
  by_cases hk : k = t.i
  · rw [if_pos hk, hk]
    simp [Matrix.mulVec, dotProduct, Matrix.single_apply, ite_mul]
  · rw [if_neg hk]
    simp [Matrix.mulVec, dotProduct, Ne.symm hk]
end PI.ProdFormulaE.HaarBox
