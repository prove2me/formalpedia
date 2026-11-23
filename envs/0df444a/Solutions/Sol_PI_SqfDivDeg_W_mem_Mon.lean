-- Prove2me | solution 1 for PI.SqfDivDeg.W.mem_Mon
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:54:09.804781+00:00
-- url     : https://prove2.me/submissions/30aa8d6c-0586-4106-b23e-1423e7089351

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SqfLab
import Definitions.Def_Formalism_PeriodIntegrals_SqfDivDeg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeDivisorDegree_MonicFintype

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open PI PI.SqfDivDeg PI.SqfDivDeg.W
namespace PI.SqfDivDeg.W
theorem _root_.solution {g : ℕ} [Fact g.Prime] {n : ℕ} {p : (ZMod g)[X]} :
    p ∈ Mon g n ↔ p.Monic ∧ p.natDegree = n := by
  simp [Mon]
end PI.SqfDivDeg.W
