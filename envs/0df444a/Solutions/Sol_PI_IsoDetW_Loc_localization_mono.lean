-- Prove2me | solution 1 for PI.IsoDetW.Loc.localization_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:33:53.80342+00:00
-- url     : https://prove2.me/submissions/33a40142-a452-4a9a-a9cb-a3d5811a184a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsoDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LidxAntisymm

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
theorem _root_.solution {A B : Submodule R W} (h : A ≤ B) : localization₂ p A ≤ localization₂ p B :=
  fun _ ⟨s, hs, hx⟩ => ⟨s, hs, h hx⟩
end PI.IsoDetW.Loc
