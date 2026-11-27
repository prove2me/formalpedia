-- Prove2me | solution 1 for ReciprocityTheory.PGsh.thmA_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:30:40.647183+00:00
-- url     : https://prove2.me/submissions/f9ad7e09-1b32-4931-976e-25261e16080c

import Definitions.Def_ReciprocityTheory_DualLattices_TangentPairingStatement
import Definitions.Def_ReciprocityTheory_DualLattices_StThmA
import Theorems.Thm_P2M_ReciprocityTheory_PGsh_BX_evK__mul_4784bc5a7404

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
namespace ReciprocityTheory.PGsh
theorem _root_.solution (B : BX R₀) (hB3 : TangentPairingStatement B) : ThmALevelStatement B := by
  intro R' R π ξ hξ Dp N hsurj hker hsq hann hN sh th v w hs ht zh z c e₀ hsh hth hhs hht hpair
    hzh hzN
  have h3 := hB3 R' R π ξ Dp N hsurj hker hsq hann hN sh th
    (TensorProduct.map LinearMap.id (ξmul π ξ hξ) v) (TensorProduct.map LinearMap.id (ξmul π ξ hξ) w)
    hs ht zh z hsh hth hhs hht hpair hzh
  rw [B.evK_ξmul, B.evK_ξmul, hzN] at h3
  have h4 : ((e₀ : (R' : Type u)) * c - (B.ev ht v - B.ev hs w)) * ξ = 0 := by
    linear_combination h3
  have h5 := hann _ h4
  rw [← hker, RingHom.mem_ker, map_sub, map_sub] at h5
  exact sub_eq_zero.mp h5
end ReciprocityTheory.PGsh
