-- Prove2me | solution 1 for ReciprocityTheory.PGsh.DualPair.nilSurj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:35:41.954695+00:00
-- url     : https://prove2.me/submissions/4d928c2a-77c1-4e0c-ba39-79fbd8a2d8fb

import Definitions.Def_ReciprocityTheory_DualLattices_ModuliPointsState
import Definitions.Def_ReciprocityTheory_DualLattices_IsFibreSq

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
theorem _root_.solution : Dp.π.NilSurj := by
  unfold LHom.NilSurj
  exact ⟨Dp.sqZero.1, 2, Dp.sqZero.2⟩
end ReciprocityTheory.PGsh.DualPair
