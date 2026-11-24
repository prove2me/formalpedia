-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_Xpow_homog_6fdb90b2f59f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:31:37.168177+00:00
-- url     : https://prove2.me/submissions/d5bd6487-fbbd-478c-8bfc-5db8b72b3d1b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_XiPluckerCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PPluckerCover

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.PluckerAffineCover
variable {D : ℕ} (S : ProjectiveLineBundle D)
namespace GroundTheory.Heights₂.Heights.Inter.PluckerAffineCover
theorem _root_.solution (i : S.ι) (d : ℕ) :
    IsWeightedHomogeneous (wt S) (X ⟨.base, i⟩ ^ d : MRing S.YIdx) (Pi.single .base d) := by
  have := (isWeightedHomogeneous_X ℤ (wt S) (⟨.base, i⟩ : Σ k, S.YIdx k)).pow d
  convert this using 1
  funext k
  simp [Pi.single_apply]
end GroundTheory.Heights₂.Heights.Inter.PluckerAffineCover
