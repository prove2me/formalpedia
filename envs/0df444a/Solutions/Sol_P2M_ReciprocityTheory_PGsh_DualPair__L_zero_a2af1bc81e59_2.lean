-- Prove2me | solution 2 for P2M_ReciprocityTheory_PGsh_DualPair__L_zero_a2af1bc81e59
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:15:08.22437+00:00
-- url     : https://prove2.me/submissions/5756b467-307d-4961-82d7-5ad33754a2d7

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
theorem _root_.solution : Dp.μL 0 = Dp.σ.comp Dp.π :=
  LHom.ext' fun d => by show Dp.fμ 0 d = Dp.σ.1 (Dp.π.1 d); simp [fμ]
end ReciprocityTheory.PGsh.DualPair
