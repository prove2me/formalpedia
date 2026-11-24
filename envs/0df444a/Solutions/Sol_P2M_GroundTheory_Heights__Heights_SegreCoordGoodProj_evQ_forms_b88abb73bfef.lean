-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SegreCoordGoodProj_evQ_forms_b88abb73bfef
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:42:49.395902+00:00
-- url     : https://prove2.me/submissions/e54e29ba-71c1-4b1a-9fdd-e2f99f14451f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegreCoordGoodProj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegreCoordGoodProj
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SegreCoordGoodProj_evQ_segQ_ccbce2b0c3b4

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
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.SegreCoordGoodProj
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.SegreCoordGoodProj
theorem _root_.solution (P : Ideal (MRing ι)) (z : (Σ k, ι k) → ℂ) (hz : z ∈ mcPts P) {r : ℕ}
    (L : Fin r → ((k : K) → ι k) → ℚ) (j : Fin r) :
    evQ P z hz (forms (segQ P) L j) = ∑ t, (L j t : ℂ) * segre z t := by
  simp only [forms, map_sum, map_rat_smul, evQ_segQ, Rat.smul_def]
end GroundTheory.Heights₂.Heights.SegreCoordGoodProj
