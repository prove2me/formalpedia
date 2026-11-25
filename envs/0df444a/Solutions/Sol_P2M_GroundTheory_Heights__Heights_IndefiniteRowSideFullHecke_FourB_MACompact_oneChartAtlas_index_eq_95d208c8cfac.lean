-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_MACompact_oneChartAtlas_index_eq_95d208c8cfac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:37:37.489058+00:00
-- url     : https://prove2.me/submissions/9f934278-2dcd-44f5-9cad-2bce51fd5200

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_LeviFormGbPotOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_OneChartAtlasIndexEq

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
open MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo
open scoped ContDiff
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB.MACompact
variable {D : ℕ} {Ω : Set (Fin D → ℂ)}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB.MACompact
theorem _root_.solution (hΩ : IsOpen Ω) [Nonempty Ω] (j : Fin (oneChartAtlas hΩ).n) : j = j0 hΩ :=
  Fin.ext (by have h1 : j.val < 1 := j.isLt; show j.val = 0; omega)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB.MACompact
