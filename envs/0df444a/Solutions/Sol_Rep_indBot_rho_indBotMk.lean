-- Prove2me | solution 1 for Rep.indBot_rho_indBotMk
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/18ccd858-ccd6-5ec5-8ffc-c998095e50c4

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateDimensionShift
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_indBot_rho_indBotMk

set_option autoImplicit false
universe u
open CategoryTheory Rep

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000

theorem solution {k G : Type u} [CommRing k] [Group G] (A : Rep.{u} k G) (g h : G) (a : A) :
    A.indBot.ρ g (A.indBotMk h a) = A.indBotMk (h * g⁻¹) a :=
  Representation.ind_mk _ _ g h a

end S_Rep_indBot_rho_indBotMk
end P2MW
export P2MW.S_Rep_indBot_rho_indBotMk (solution)
