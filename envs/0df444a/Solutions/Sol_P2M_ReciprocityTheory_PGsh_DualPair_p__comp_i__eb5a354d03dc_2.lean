-- Prove2me | solution 2 for P2M_ReciprocityTheory_PGsh_DualPair_p__comp_i__eb5a354d03dc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:16:05.200665+00:00
-- url     : https://prove2.me/submissions/9ad6fd31-68e0-4431-8fff-d085a53deb74

import Definitions.Def_ReciprocityTheory_DualLattices_ModuliPointsState
import Definitions.Def_ReciprocityTheory_DualLattices_IsFibreSq
import Theorems.Thm_P2M_ReciprocityTheory_PGsh_LHom_ext__04d8c2f369fc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.PGsh
universe u
variable {R₀ : Type u} [CommRing R₀]
open ReciprocityTheory.PGsh.DualPair
variable {R : LAlg R₀} (Dp : DualPair R)
namespace ReciprocityTheory.PGsh.DualPair
theorem _root_.solution : Dp.p₂L.comp Dp.i₂L = LHom.id Dp.D := LHom.ext' fun _ => rfl
end ReciprocityTheory.PGsh.DualPair
