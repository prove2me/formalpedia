-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SegreCoordGoodProj_segre_scaleBlock_124690bb4980
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:52:47.208034+00:00
-- url     : https://prove2.me/submissions/efd11359-4cdc-4483-a74d-c16429328986

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegreCoordGoodProj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegreCoordGoodProj

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
omit [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.SegreCoordGoodProj
theorem _root_.solution (k0 : K) (c : ℂ) (z : (Σ k, ι k) → ℂ) (t : (k : K) → ι k) :
    segre (scaleBlock k0 c z) t = c * segre z t := by
  simp only [segre, scaleBlock, Finset.prod_mul_distrib]
  congr 1
  simp
end GroundTheory.Heights₂.Heights.SegreCoordGoodProj
