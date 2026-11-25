-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.SplitGL.ext_p
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:58:28.012817+00:00
-- url     : https://prove2.me/submissions/68f5bf53-6afb-47a1-bcf7-956e46c086e4

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Commensurated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_SplitGL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq PI.UnitaryGroupMassFormula.AdIndexEq.SplitGL
open Matrix
variable {R k : Type} [CommRing R] [Field k] {n : Type} [Fintype n] [DecidableEq n]
namespace PI.UnitaryGroupMassFormula.AdIndexEq.SplitGL
theorem _root_.solution (π : R ≃+* k × k) {r s : R} (h1 : p1 π r = p1 π s) (h2 : p2 π r = p2 π s) : r = s := by
  apply π.injective
  exact Prod.ext h1 h2
end PI.UnitaryGroupMassFormula.AdIndexEq.SplitGL
