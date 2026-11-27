-- Prove2me | solution 2 for P2M_ReciprocityTheory_PGsh_DualPair__A___46a3cd182ba4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:15:23.180986+00:00
-- url     : https://prove2.me/submissions/56ea04cb-25bc-45e6-9f9c-b0c26662f582

import Definitions.Def_ReciprocityTheory_DualLattices_ModuliPointsState
import Definitions.Def_ReciprocityTheory_DualLattices_IsFibreSq
import Theorems.Thm_P2M_ReciprocityTheory_PGsh_DualPair_____9b8197f73975

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
theorem _root_.solution (c : (R : Type u)) : Dp.μA c Dp.η = Dp.σ.1 c * Dp.η := by
  simp [μA_apply, fμ, Dp.π_η]
end ReciprocityTheory.PGsh.DualPair
