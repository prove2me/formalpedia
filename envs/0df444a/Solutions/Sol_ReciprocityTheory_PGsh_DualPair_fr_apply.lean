-- Prove2me | solution 1 for ReciprocityTheory.PGsh.DualPair.fr_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:26:11.273189+00:00
-- url     : https://prove2.me/submissions/cd18c985-4f80-4972-857f-2cfb661165af

import Definitions.Def_ReciprocityTheory_DualLattices_ModuliPointsState
import Definitions.Def_ReciprocityTheory_DualLattices_NilSurjOfSqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct
open ReciprocityTheory ReciprocityTheory.PGsh
universe u
variable {R₀ : Type u} [CommRing R₀]
open ReciprocityTheory.PGsh.DualPair
variable {R : LAlg R₀} (Dp : DualPair R)
namespace ReciprocityTheory.PGsh.DualPair
theorem _root_.solution (r : (R : Type u)) (b : (Dp.D : Type u)) :
    (Dp.fr r).1 b = Dp.σ.1 (Dp.π.1 b) + Dp.σ.1 (Dp.κ b * r) * Dp.η := rfl
end ReciprocityTheory.PGsh.DualPair
