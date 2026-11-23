-- Prove2me | solution 1 for PI.IsoDetW.Loc.lidx_antisymm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:30:59.484876+00:00
-- url     : https://prove2.me/submissions/8cce0791-febc-49f0-aa8d-5d372d0eb1ee

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsoDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LidxAntisymm
import Theorems.Thm_PI_IsoDetW_Loc_lidx_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.IsoDetW PI.IsoDetW.Loc
open PI.IsoDetDefs
variable {R : Type*} [CommRing R] {W : Type*} [AddCommGroup W] [Module R W]
variable (p : Ideal R) [p.IsPrime]
namespace PI.IsoDetW.Loc
theorem _root_.solution (A B : Submodule R W) : lidx p A B = - lidx p B A := by
  rw [lidx_eq, lidx_eq, inf_comm]; ring
end PI.IsoDetW.Loc
