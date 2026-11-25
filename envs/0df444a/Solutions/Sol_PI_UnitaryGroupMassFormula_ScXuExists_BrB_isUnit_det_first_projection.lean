-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ScXuExists.BrB.isUnit_det_first_projection
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:53:52.609813+00:00
-- url     : https://prove2.me/submissions/5bceca67-a516-4636-87a2-693ad294385d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_SplitGL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_SecondProjectionSplitEquiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ScXuExists PI.UnitaryGroupMassFormula.ScXuExists.BrB
open Matrix PI.UnitaryGroupMassFormula.AdIndexEq
namespace PI.UnitaryGroupMassFormula.ScXuExists.BrB
theorem _root_.solution {R k : Type} [CommRing R] [Field k] {n : Type} [Fintype n] [DecidableEq n]
    (π : R ≃+* k × k) (J : Matrix n n R) (hdet : IsUnit J.det) : IsUnit (J.map (SplitGL.p1 π)).det := by
  show IsUnit ((SplitGL.p1 π).mapMatrix J).det
  rw [← RingHom.map_det]
  exact hdet.map _
end PI.UnitaryGroupMassFormula.ScXuExists.BrB
