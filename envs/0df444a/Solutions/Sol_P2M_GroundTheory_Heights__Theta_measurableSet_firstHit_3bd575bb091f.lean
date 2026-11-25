-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_measurableSet_firstHit_3bd575bb091f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:54:31.526152+00:00
-- url     : https://prove2.me/submissions/a8dc4af6-308b-4ef6-a3a2-b084cfbe54d3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_FundDomain
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_isOpen_saturate_bdd42cb5cc08

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Topology
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [LocallyCompactSpace G]
namespace GroundTheory.Heights₂.Theta
theorem _root_.solution [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G)
    {A : ℕ → Set G} (hA : ∀ i, IsOpen (A i)) : MeasurableSet (firstHit Γ A) := by
  refine MeasurableSet.iUnion fun i => (hA i).measurableSet.diff ?_
  exact (isOpen_saturate Γ (isOpen_biUnion fun j _ => hA j)).measurableSet
end GroundTheory.Heights₂.Theta
