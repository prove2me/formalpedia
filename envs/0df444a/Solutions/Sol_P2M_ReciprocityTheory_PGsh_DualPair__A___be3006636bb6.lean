-- Prove2me | solution 1 for P2M_ReciprocityTheory_PGsh_DualPair__A___be3006636bb6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:01:35.642525+00:00
-- url     : https://prove2.me/submissions/b71ed77c-369d-4095-9e71-fb3bee78cecc

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
theorem _root_.solution (c r : (R : Type u)) : Dp.μA c (Dp.σ.1 r) = Dp.σ.1 r := by
  simp [μA_apply, fμ, Dp.sect]
end ReciprocityTheory.PGsh.DualPair
