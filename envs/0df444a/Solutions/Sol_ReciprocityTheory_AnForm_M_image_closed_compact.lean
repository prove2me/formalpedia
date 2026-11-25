-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.image_closed_compact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:24:37.50609+00:00
-- url     : https://prove2.me/submissions/5aea55a9-dcb7-41e0-b588-246157efb69f

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_MaMeasureA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_MaMeasureB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Set Filter Topology
open scoped ContDiff ENNReal NNReal
noncomputable section
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X]
    (ch : OpenPartialHomeomorph X (Fin e → ℂ)) {Z : Set X} (hZ : IsClosed Z)
    (hZs : Z ⊆ ch.source) : IsCompact (ch '' Z) ∧ ch '' Z ⊆ ch.target :=
  ⟨hZ.isCompact.image_of_continuousOn (ch.continuousOn.mono hZs), by
    rintro _ ⟨x, hx, rfl⟩
    exact ch.map_source (hZs hx)⟩
end ReciprocityTheory.AnForm.M
