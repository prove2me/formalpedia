-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kleiman_chartRingI_singleton_d9061a633ff5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:28:12.96634+00:00
-- url     : https://prove2.me/submissions/4207749b-0221-4452-9364-14ee1827e3f7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_Bundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CoordIdealIsMultiProjPrime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman
open MvPolynomial
noncomputable section
open ReciprocityTheory.ChartRestriction.G.Geo
variable (S : Type) [CommRing S] {N : ℕ} {Ω : Type} [Field Ω] [Algebra S Ω]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman
theorem _root_.solution (x : Fin (N + 1) → Ω) (i : Fin (N + 1)) :
    chartRingI S x {i} = chartRing S x i := by
  unfold chartRingI chartRing
  congr 1
  ext y
  simp [eq_comm]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman
