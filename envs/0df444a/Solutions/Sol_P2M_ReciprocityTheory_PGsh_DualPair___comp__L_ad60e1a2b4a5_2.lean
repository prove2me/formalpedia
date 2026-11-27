-- Prove2me | solution 2 for P2M_ReciprocityTheory_PGsh_DualPair___comp__L_ad60e1a2b4a5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:15:13.713363+00:00
-- url     : https://prove2.me/submissions/63782604-83f0-41de-8435-3d79597d1360

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
theorem _root_.solution (c : (R : Type u)) : Dp.π.comp (Dp.μL c) = Dp.π :=
  LHom.ext' fun d => Dp.π_μA c d
end ReciprocityTheory.PGsh.DualPair
