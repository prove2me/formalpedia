-- Prove2me | solution 1 for ReciprocityTheory.PGsh.DualPair.mr_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:34:07.819726+00:00
-- url     : https://prove2.me/submissions/fc864645-12f5-421f-ad16-1881a57ab6a9

import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_IsPairingValueAddRight
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemSpan

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
theorem _root_.solution (r : (R : Type u)) (d : (Dp.D : Type u)) :
    (Dp.mr r).1 d = Dp.σ.1 (Dp.π.1 d) + Dp.σ.1 r * (d - Dp.σ.1 (Dp.π.1 d)) := rfl
end ReciprocityTheory.PGsh.DualPair
