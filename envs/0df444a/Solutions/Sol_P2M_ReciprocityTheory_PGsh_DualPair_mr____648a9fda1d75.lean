-- Prove2me | solution 1 for P2M_ReciprocityTheory_PGsh_DualPair_mr____648a9fda1d75
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:01:57.459877+00:00
-- url     : https://prove2.me/submissions/81400629-632c-4ce2-9894-3f2b3f5bf1b1

import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_IsPairingValueAddRight
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemSpan
import Theorems.Thm_P2M_RH_P2M_ReciprocityTheory_PGsh_DualPair_____9b8197f73975_35ac38284c5cda63
import Theorems.Thm_ReciprocityTheory_PGsh_DualPair_mr_apply

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
theorem _root_.solution (r t : (R : Type u)) :
    (Dp.mr r).1 (Dp.σ.1 t * Dp.η) = Dp.σ.1 r * (Dp.σ.1 t * Dp.η) := by
  simp [mr_apply, Dp.π_η]
end ReciprocityTheory.PGsh.DualPair
