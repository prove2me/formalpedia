-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmBorderFull.bL_last
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:47:10.989986+00:00
-- url     : https://prove2.me/submissions/4d4f4be5-a3a7-4edb-8dbb-692e43f53d2d

import Definitions.Def_Formalism_PeriodIntegrals_QmBorderFull
import Definitions.Def_Formalism_PeriodIntegrals_QmBorderES
import Definitions.Def_Formalism_PeriodIntegrals_QmColExp
import Definitions.Def_Formalism_PeriodIntegrals_QmRowExp
import Definitions.Def_Formalism_PeriodIntegrals_QmSkip
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderMinorRotation_Development

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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.QmBorderFull
open PI
namespace PI.UnitaryGroupMassFormula.QmBorderFull
theorem _root_.solution {n m : ℕ} (e es : Fin n) (v : Fin m → Fin n) :
    bE e (bS v es) ∘ (Fin.last (m + 1)).succAbove = bE e v := by
  funext i
  simp only [Function.comp_apply, Fin.succAbove_last]
  cases i using Fin.cases with
  | zero => simp [PI.bE]
  | succ j =>
    first
    | simp [PI.bE, PI.bS, ← Fin.succ_castSucc]
    | simp [PI.bE, PI.bS, Fin.cons_snoc_eq_snoc_cons]
end PI.UnitaryGroupMassFormula.QmBorderFull
