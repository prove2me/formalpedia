-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_regRing_intCast_coe_2b169ec58805
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:03:36.629834+00:00
-- url     : https://prove2.me/submissions/20ae8490-5c17-4b7f-9d4a-41d0ed5d315e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsMoreFurther
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsMoreAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IntCastMemRegMaxAt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LeOfHeightMapEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FunFieldExistsInv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution (P : Ideal (MRing ι)) (n : ℤ) :
    (((n : regRing P) : funField P) : FractionRing (MRing ι ⧸ P)) =
      algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P (C n)) := by
  rw [eq_intCast C n, map_intCast, map_intCast]
  simp
end GroundTheory.Heights₂.Heights.Inter
