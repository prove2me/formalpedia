-- Prove2me | solution 1 for ReciprocityTheory.PGsh.DualPair.mr_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:38:17.165393+00:00
-- url     : https://prove2.me/submissions/86903f33-3837-4a07-a343-df67ce5c8b60

import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_IsPairingValueAddRight
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemSpan
import Theorems.Thm_P2M_ReciprocityTheory_PGsh_DualPair_mr___4f4cf4efc828

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
theorem _root_.solution (r : (R : Type u)) :
    ∀ a ∈ Dp.π.ker, (Dp.mr r).1.toLinearMap a ∈ Dp.π.ker := by
  intro a ha
  rw [Submodule.restrictScalars_mem, RingHom.mem_ker] at ha ⊢
  rw [AlgHom.toLinearMap_apply, Dp.mr_π, ha]
end ReciprocityTheory.PGsh.DualPair
