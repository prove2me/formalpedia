-- Prove2me | solution 1 for P2M_ReciprocityTheory_PGsh_BX_evK__mul_4784bc5a7404
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:01:25.074805+00:00
-- url     : https://prove2.me/submissions/18f1c444-e975-447d-865c-b62305549400

import Definitions.Def_ReciprocityTheory_DualLattices_TangentPairingStatement
import Definitions.Def_ReciprocityTheory_DualLattices_StThmA

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
open ReciprocityTheory.PGsh.BX
variable (B : BX R₀)
namespace ReciprocityTheory.PGsh.BX
theorem _root_.solution {R' R : LAlg R₀} (π : LHom R' R) (ξ : (R' : Type u)) (hξ : ξ ∈ π.ker)
    (h : B.gg →ₗ[R₀] R') (v : B.gg ⊗[R₀] (R' : Type u)) :
    B.evK π h (TensorProduct.map LinearMap.id (ξmul π ξ hξ) v) = ξ * B.ev h v := by
  induction v using TensorProduct.induction_on with
  | zero => simp [evK, ev]
  | tmul g r =>
    simp only [evK, ev, TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.mul'_apply,
      Submodule.subtype_apply]
    show h g * (ξ * r) = ξ * (h g * r)
    ring
  | add x y hx hy =>
    simp only [evK, ev, map_add] at hx hy ⊢
    rw [hx, hy, mul_add]
end ReciprocityTheory.PGsh.BX
