-- Prove2me | solution 1 for Rep.indBotPi_indBotMk
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/bd965899-b59a-57f8-9109-cdbeda2615ad

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateDimensionShift
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_indBotPi_indBotMk

set_option autoImplicit false
universe u
open CategoryTheory Rep

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000

theorem solution {k G : Type u} [CommRing k] [Group G] (A : Rep.{u} k G) (g : G) (a : A) :
    (Rep.indBotπ A).hom (A.indBotMk g a) = A.ρ g⁻¹ a := by
  simp [Rep.indBotπ, Rep.indBotMk, Rep.indResHomEquiv]

end S_Rep_indBotPi_indBotMk
end P2MW
export P2MW.S_Rep_indBotPi_indBotMk (solution)
