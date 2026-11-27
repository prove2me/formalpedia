-- Prove2me | solution 2 for P2M_ReciprocityTheory_PGsh_DualPair_p__comp_g_f3bf496f6b15
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:15:32.738528+00:00
-- url     : https://prove2.me/submissions/c5902b48-e2d0-4839-9db5-85a71a2f8920

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
theorem _root_.solution (c : (R : Type u)) : Dp.p₁L.comp (Dp.gL c) = Dp.μL c := LHom.ext' fun _ => rfl
end ReciprocityTheory.PGsh.DualPair
