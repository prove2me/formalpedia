-- Prove2me | solution 1 for Rep.indBotMap_indBotMk
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/a942a4e2-202e-51a0-82a3-29b008aedbb2

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateDimensionShift
import Definitions.Def_GroupCohomology_TateDimensionShiftMaps
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_indBotMap_indBotMk

set_option autoImplicit false
universe u
p2m_open "CategoryTheory Rep CategoryTheory.MonoidalCategory"

theorem solution {k G : Type u} [CommRing k] [Group G] {A B : Rep.{u} k G} (φ : A ⟶ B) (g : G) (a : A) :
    (Rep.indBotMap φ).hom (A.indBotMk g a) = B.indBotMk g (φ.hom a) := by
  rfl

end S_Rep_indBotMap_indBotMk
end P2MW
export P2MW.S_Rep_indBotMap_indBotMk (solution)
