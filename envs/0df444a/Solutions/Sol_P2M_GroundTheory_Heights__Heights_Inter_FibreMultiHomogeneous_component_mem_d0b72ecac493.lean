-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_FibreMultiHomogeneous_component_mem_d0b72ecac493
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:33:34.253071+00:00
-- url     : https://prove2.me/submissions/67fb8876-e952-4e96-8efa-b26eb8c4a78d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsMoreLast
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsMultiProjPrimeImageZ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CycDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LiftZComponent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_FibreMultiHomogeneous_component_map_472fbc4efe30
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PointVertical_mem_map_red_iff_50299f2085c4
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_cyc_isHomogeneous_of_isMultiHomogIdeal


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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
attribute [local instance] MvPolynomial.weightedGradedAlgebra
open GroundTheory.Heights₂.Heights.Inter.FibreMultiHomogeneous
variable {K : Type} {ι : K → Type} {K' : Type} {ι' : K' → Type}
namespace GroundTheory.Heights₂.Heights.Inter.FibreMultiHomogeneous
theorem _root_.solution [Fintype K'] [∀ k, Fintype (ι' k)] {p : ℕ} {W' : Ideal (MRing ι')} (hp : ((p : ℕ) : MRing ι') ∈ W')
    (hW : IsMultiHomogIdeal (W'.map (MvPolynomial.map (Int.castRingHom (ZMod p))))) [DecidableEq K'] (k : K')
    (n : ℕ) {g : MRing ι'} (hg : g ∈ W') : weightedHomogeneousComponent (cycBlockWt k) n g ∈ W' := by
  rw [← PointVertical.mem_map_red_iff p hp, PointVertical.red, ← component_map]
  exact weightedHomogeneousComponent_mem_of_mem _ _ (cyc_isHomogeneous_of_isMultiHomogIdeal hW k)
    ((PointVertical.mem_map_red_iff p hp g).2 hg) n
end GroundTheory.Heights₂.Heights.Inter.FibreMultiHomogeneous
