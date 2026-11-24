-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity___apply_a3d15408a314
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:45:45.980661+00:00
-- url     : https://prove2.me/submissions/945971b3-1192-41c8-86b5-93d4259df57b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ImportsAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LengthLocalizedModuleQuotient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.ObjectsChow
open GroundTheory.Heights₂.Heights.ObjectsChow.VerticalPartMultiplicity
open MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk Xc)
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.ObjectsChow.VerticalPartMultiplicity
theorem _root_.solution (f : MRing (PBlk n)) :
    Ψ n f = MvPolynomial.map (ι : ℤ →+* 𝓞 ℚ) (rename (eb n).symm f) := rfl
end GroundTheory.Heights₂.Heights.ObjectsChow.VerticalPartMultiplicity
