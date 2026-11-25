-- Prove2me | solution 1 for ReciprocityTheory.PGsh.bx_heightFunctional
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:37:00.338322+00:00
-- url     : https://prove2.me/submissions/37e0f44d-284b-46a2-8721-bca40f33cfe3

import Definitions.Def_ReciprocityTheory_DualLattices_IsPairingValueAddRight
import Definitions.Def_ReciprocityTheory_DualLattices_HeightFunctionalStatementOfPairingProperties
import Definitions.Def_ReciprocityTheory_DualLattices_TangentPairingStatementOfHeightFunctional
import Definitions.Def_ReciprocityTheory_DualLattices_ThmAFull
import Definitions.Def_ReciprocityTheory_DualLattices_AinfTower
import Definitions.Def_ReciprocityTheory_DualLattices_ThmAAll
import Theorems.Thm_ReciprocityTheory_PGsh_heightFunctionalStatement_of_pairingProperties
import Theorems.Thm_ReciprocityTheory_PGsh_pairingProperties


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.PGsh
namespace ReciprocityTheory.PGsh
theorem _root_.solution {R₀ : Type*} [CommRing R₀] (B : BX R₀) : HighestWeightVectorUniformBounds B := heightFunctionalStatement_of_pairingProperties B (pairingProperties B)
end ReciprocityTheory.PGsh
