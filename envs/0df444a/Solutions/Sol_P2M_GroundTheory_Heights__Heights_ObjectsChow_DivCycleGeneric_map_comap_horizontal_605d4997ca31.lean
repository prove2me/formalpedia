-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsChow_DivCycleGeneric_map_comap_horizontal_605d4997ca31
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:45:08.819606+00:00
-- url     : https://prove2.me/submissions/0db770af-76a0-4828-9820-47227506a948

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ImportsAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PObjectsDivCycleGeneric
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_DivCycleGeneric_disjoint_iff_isHorizontal_a353c136abe0

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
open GroundTheory.Heights₂.Heights.ObjectsChow.DivCycleGeneric
open MvPolynomial
variable {n : ℕ}
attribute [local instance] genericAlgebra
namespace GroundTheory.Heights₂.Heights.ObjectsChow.DivCycleGeneric
theorem _root_.solution (W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestriction.G.Geo.PBlk n)))
    (hW : W.IsPrime) (hh : ReciprocityTheory.ChartRestriction.G.Geo.IsHorizontal W) :
    (W.map (algebraMap _ (MvPolynomial (Fin n) ℚ))).comap (algebraMap _ (MvPolynomial (Fin n) ℚ)) = W :=
  IsLocalization.under_map_of_isPrime_disjoint (intUnits n) (MvPolynomial (Fin n) ℚ) hW
    ((disjoint_iff_isHorizontal W).mpr hh)
end GroundTheory.Heights₂.Heights.ObjectsChow.DivCycleGeneric
