-- Prove2me | solution 1 for PI.SqfDivDeg.W.card_Mon
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:54:12.739175+00:00
-- url     : https://prove2.me/submissions/244aaded-8f47-400e-aa14-e2f082a54c1f

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
theorem _root_.solution (g : ℕ) [Fact g.Prime] (n : ℕ) : (Mon g n).card = g ^ n := by
  rw [Mon, Finset.card_map, Finset.card_univ,
    Fintype.card_congr ((monicEquivDegreeLT n).trans (degreeLTEquiv (ZMod g) n).toEquiv)]
  simp
end PI.SqfDivDeg.W
