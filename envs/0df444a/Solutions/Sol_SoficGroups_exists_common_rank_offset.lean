-- Prove2me | solution 1 for SoficGroups.exists_common_rank_offset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:52.29415+00:00
-- url     : https://prove2.me/submissions/26860c69-7363-4ca1-a1c2-26e20354ab20

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_exists_common_offset_below_average
import Theorems.Thm_SoficGroups_integrableOn_rankDropCount

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution {ι : Type*} [Fintype ι]
    (u v : ι → ℝ) (H : ℝ) (hH : 0 < H) :
    ∃ r ∈ Set.Ico 0 H,
      rankDropCount u v H r ≤
        MeasureTheory.average
          (MeasureTheory.volume.restrict (Set.Ico 0 H))
          (fun t : ℝ => rankDropCount u v H t) := by
  exact exists_common_offset_below_average H hH
    (fun t : ℝ => rankDropCount u v H t)
    (integrableOn_rankDropCount u v H)
end SoficGroups
