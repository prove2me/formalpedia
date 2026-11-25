-- Prove2me | solution 1 for ReciprocityTheory.PGsh.pairingProperties
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:18:51.97144+00:00
-- url     : https://prove2.me/submissions/6e5a3b3e-7cbc-429c-a47e-8046b706864c

import Definitions.Def_ReciprocityTheory_DualLattices_SeriesState
import Definitions.Def_ReciprocityTheory_DualLattices_InstAddCommMonoidFibreFst
import Definitions.Def_ReciprocityTheory_DualLattices_NsmulFstAddSnd
import Definitions.Def_ReciprocityTheory_DualLattices_IsPairingValueAddRight
import Theorems.Thm_ReciprocityTheory_PGsh_BX_pairing_exists
import Theorems.Thm_ReciprocityTheory_PGsh_BX_pairing_unique
import Theorems.Thm_ReciprocityTheory_PGsh_BX_isPairingValue_add_left
import Theorems.Thm_ReciprocityTheory_PGsh_BX_isPairingValue_add_right
import Theorems.Thm_ReciprocityTheory_PGsh_BX_pairing_sw
import Theorems.Thm_ReciprocityTheory_PGsh_BX_pairing_pow
import Theorems.Thm_ReciprocityTheory_PGsh_BX_pairing_map
import Theorems.Thm_ReciprocityTheory_PGsh_BX_pairing_mul

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
namespace ReciprocityTheory.PGsh
theorem _root_.solution (B : BX R₀) : PairingPropertiesStatement B := by
  refine ⟨fun R N x y hx hy => B.pairing_exists N x y hx hy,
    fun R N x y z z' h h' => B.pairing_unique N x y z z' h h',
    fun R N x x' y z z' w h h' hw => B.pairing_unique N _ _ _ _ hw (B.isPairingValue_add_left N x x' y z z' h h'),
    fun R N x y y' z z' w h h' hw => B.pairing_unique N _ _ _ _ hw (B.isPairingValue_add_right N x y y' z z' h h'),
    fun R N x y z z' h h' => ?_, fun R N x y z h => B.pairing_pow N x y z h,
    fun R S f N x y z h => B.pairing_map f N x y z h,
    fun R N p x y z hx hy h => B.pairing_mul N p x y z hx hy h⟩
  rw [← B.pairing_unique N y x _ _ (B.pairing_sw N x y z h) h', mul_inv_cancel]
end ReciprocityTheory.PGsh
