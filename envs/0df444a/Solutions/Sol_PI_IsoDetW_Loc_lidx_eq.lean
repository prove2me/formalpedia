-- Prove2me | solution 1 for PI.IsoDetW.Loc.lidx_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:27:42.404923+00:00
-- url     : https://prove2.me/submissions/b2f067d4-7271-418e-8880-b995a6cd9e5e

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
theorem _root_.solution (A B : Submodule R W) :
    lidx p A B = ((relative₂ (localization₂ p (A ⊓ B)) (localization₂ p A)).toNat : ℤ) - (relative₂ (localization₂ p (A ⊓ B)) (localization₂ p B)).toNat :=
  rfl
end PI.IsoDetW.Loc
