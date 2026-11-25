-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.SplitGL.mat_ext_p
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:17:53.79881+00:00
-- url     : https://prove2.me/submissions/b055301d-ceeb-475e-bd19-d010baa7dbde

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Commensurated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_SplitGL
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_SplitGL_ext_p

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
theorem _root_.solution (π : R ≃+* k × k) {M N : Matrix n n R} (h1 : M.map (p1 π) = N.map (p1 π))
    (h2 : M.map (p2 π) = N.map (p2 π)) : M = N := by
  ext i j
  exact ext_p π (congrFun (congrFun h1 i) j) (congrFun (congrFun h2 i) j)
end PI.UnitaryGroupMassFormula.AdIndexEq.SplitGL
