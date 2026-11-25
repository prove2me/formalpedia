-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ProjRankTransfer_locallyConnectedSpace_b33ab8750658
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:08:12.593229+00:00
-- url     : https://prove2.me/submissions/4b87809a-ba2f-434b-b19b-25bca2d5877a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRankTransfer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjPotMassPos
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjPotDensVanish
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjRankTransfer

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M
namespace GroundTheory.Heights₂.Heights.Targets
namespace ProjRankTransfer
theorem _root_.solution {e : ℕ} {X : Type*} [TopologicalSpace X]
    (A : FinHolAtlas e X) : LocallyConnectedSpace X := by
  let _ : ChartedSpace (Fin e → ℂ) X :=
    { atlas := Set.range A.chart
      chartAt := fun x => A.chart (chartIdx A x)
      mem_chart_source := fun x => Classical.choose_spec (A.cover x)
      chart_mem_atlas := fun x => ⟨_, rfl⟩ }
  exact ChartedSpace.locallyConnectedSpace (Fin e → ℂ) X
end ProjRankTransfer
end GroundTheory.Heights₂.Heights.Targets
