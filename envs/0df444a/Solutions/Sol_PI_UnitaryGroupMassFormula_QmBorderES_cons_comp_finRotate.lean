-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmBorderES.cons_comp_finRotate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:41:39.272544+00:00
-- url     : https://prove2.me/submissions/f12d42eb-0003-4991-983b-489a3cb929c5

import Definitions.Def_Formalism_PeriodIntegrals_QmBorderES
import Definitions.Def_Formalism_PeriodIntegrals_QmColExp
import Definitions.Def_Formalism_PeriodIntegrals_QmRowExp
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderSignIdentity_SkipOneEqSuccAbove

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
theorem _root_.solution {n t : ℕ} (e : Fin n) (f : Fin t → Fin n) :
    PI.bE e f ∘ (finRotate (t + 1) : Fin (t + 1) → Fin (t + 1)) = PI.bS f e := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [PI.bE, PI.bS, finRotate_succ_apply, Fin.last_add_one]
  · simp [PI.bE, PI.bS, finRotate_succ_apply, Fin.coeSucc_eq_succ]
end PI.UnitaryGroupMassFormula.QmBorderES
