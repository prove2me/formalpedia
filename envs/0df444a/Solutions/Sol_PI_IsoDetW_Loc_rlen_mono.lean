-- Prove2me | solution 1 for PI.IsoDetW.Loc.rlen_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:34:50.210226+00:00
-- url     : https://prove2.me/submissions/e753005c-0902-4fc3-85d9-47172bac6dc3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsoDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LidxAntisymm
import Theorems.Thm_PI_IsoDetW_Loc_rlen_add

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
namespace PI.IsoDetW.Loc
theorem _root_.solution {X X' Z Z' : Submodule R W} (hX : X' ≤ X) (hXZ : X ≤ Z) (hZ : Z ≤ Z') :
    relative₂ X Z ≤ relative₂ X' Z' := by
  rw [rlen_add hX (hXZ.trans hZ), rlen_add hXZ hZ]
  calc relative₂ X Z ≤ relative₂ X Z + relative₂ Z Z' := le_self_add
    _ ≤ relative₂ X' X + (relative₂ X Z + relative₂ Z Z') := le_add_self
end PI.IsoDetW.Loc
