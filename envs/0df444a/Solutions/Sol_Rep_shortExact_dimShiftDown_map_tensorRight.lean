-- Prove2me | solution 1 for Rep.shortExact_dimShiftDown_map_tensorRight
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/a33e5920-76f5-5030-b978-a1c8a8921216

import Mathlib
import Definitions.Def_GroupCohomology_TateDimensionShift
import Theorems.Thm_Rep_dimShiftDown_shortExact
import Theorems.Thm_Rep_indBotPi_indBotSigma
import Theorems.Thm_Rep_shortExact_map_tensorRight_of_splitting
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_shortExact_dimShiftDown_map_tensorRight

set_option autoImplicit false
universe u
p2m_open "CategoryTheory Rep CategoryTheory.MonoidalCategory"

theorem solution {k G : Type u} [CommRing k] [Group G] (A B : Rep.{u} k G) :
    (A.dimShiftDown.map (MonoidalCategory.tensorRight B)).ShortExact := by
  exact Rep.shortExact_map_tensorRight_of_splitting (Rep.dimShiftDown_shortExact A) A.indBotσ
    (fun a => Rep.indBotPi_indBotSigma A a) B

end S_Rep_shortExact_dimShiftDown_map_tensorRight
end P2MW
export P2MW.S_Rep_shortExact_dimShiftDown_map_tensorRight (solution)
