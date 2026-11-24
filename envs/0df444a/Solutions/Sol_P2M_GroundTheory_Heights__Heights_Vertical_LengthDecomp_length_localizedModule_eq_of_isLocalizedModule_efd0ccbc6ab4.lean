-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_LengthDecomp_length_localizedModule_eq_of_isLocalizedModule_efd0ccbc6ab4
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:40:06.839723+00:00
-- url     : https://prove2.me/submissions/a70d1512-d272-4512-b0ac-193700f2857b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PLengthDecomp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open Module IsLocalRing LinearMap Submodule
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.LengthDecomp
open Classical
variable {B : Type*} [CommRing B]
namespace GroundTheory.Heights₂.Heights.Vertical.LengthDecomp
theorem _root_.solution (p : Ideal B) [p.IsPrime]
    {X Y : Type*} [AddCommGroup X] [Module B X] [AddCommGroup Y] [Module B Y]
    [Module (Localization.AtPrime p) Y] [IsScalarTower B (Localization.AtPrime p) Y]
    (g : X →ₗ[B] Y) [IsLocalizedModule p.primeCompl g] :
    length (Localization.AtPrime p) (LocalizedModule p.primeCompl X) =
      length (Localization.AtPrime p) Y :=
  ((IsLocalizedModule.iso p.primeCompl g).extendScalarsOfIsLocalization p.primeCompl
    (Localization.AtPrime p)).length_eq
end GroundTheory.Heights₂.Heights.Vertical.LengthDecomp
