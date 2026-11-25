-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_funFieldEquiv_image_chartRing_1d48bb1173f5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:21:44.738101+00:00
-- url     : https://prove2.me/submissions/535172d6-5f5b-4610-a335-5f2b90b5f4f6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_FunFieldEquivMemChartRingIff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_funFieldEquiv_chartCoord_05900769c4a7

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
open MvPolynomial
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [Fintype ι]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
theorem _root_.solution (P : ArithVariety n) (c : (k : ι) → Fin (n k + 1)) :
    funFieldEquiv P '' (P.chartRing c : Set P.FunField) = (chartRing P c : Set (FunField P)) := by
  have hmap := RingHom.map_closure (funFieldEquiv P).toRingHom (Set.range (P.chartCoord c))
  have hrange : (funFieldEquiv P).toRingHom '' Set.range (P.chartCoord c) =
      Set.range fun p : Coord n ↦ genPt P p / genPt P ⟨p.1, c p.1⟩ := by
    rw [← Set.range_comp]
    congr 1
    funext v
    exact funFieldEquiv_chartCoord P c v
  rw [hrange] at hmap
  rw [chartRing, ReciprocityTheory.ChartRestriction.G.Geo.chartRingZ, Algebra.adjoin_int, ← hmap]
  rfl
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
