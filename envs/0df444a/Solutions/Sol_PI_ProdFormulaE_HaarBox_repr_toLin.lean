-- Prove2me | solution 1 for PI.ProdFormulaE.HaarBox.repr_toLin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:11:32.136561+00:00
-- url     : https://prove2.me/submissions/a98227ab-be08-4e56-ba05-ca77bfe2cbc2

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
theorem _root_.solution (b : Basis ι K E) (A : Matrix ι ι K) (x : E) :
    b.repr (Matrix.toLin b b A x) = A *ᵥ b.repr x := by
  have h := LinearMap.toMatrix_mulVec_repr b b (Matrix.toLin b b A) x
  rw [LinearMap.toMatrix_toLin] at h
  exact h.symm
end PI.ProdFormulaE.HaarBox
