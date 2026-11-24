-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_Bundles_pt_sub_621877caaca7
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:55:55.534135+00:00
-- url     : https://prove2.me/submissions/a8d57295-0dba-4764-9a08-777f1e678d4c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_InstFintypeSumElim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ScaledRankOneLeStandardRankOne

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
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
variable {Ω : Type*} [Field Ω]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
theorem _root_.solution : ∀ k, Subsingleton (ptIdx k) := fun _ => inferInstanceAs (Subsingleton (Fin 1))
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
