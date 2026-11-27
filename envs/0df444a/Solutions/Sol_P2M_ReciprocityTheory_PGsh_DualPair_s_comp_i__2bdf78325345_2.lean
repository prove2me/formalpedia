-- Prove2me | solution 2 for P2M_ReciprocityTheory_PGsh_DualPair_s_comp_i__2bdf78325345
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:15:37.662836+00:00
-- url     : https://prove2.me/submissions/57a0cb82-8f57-483b-a4c6-779d01538894

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
theorem _root_.solution : Dp.sL.comp Dp.i₁L = LHom.id Dp.D := LHom.ext' fun d => by
  show d + Dp.σ.1 (Dp.π.1 d) - Dp.σ.1 (Dp.π.1 d) = d
  ring
end ReciprocityTheory.PGsh.DualPair
