-- Prove2me | solution 1 for ReciprocityTheory.PGsh.OAdj.ht_a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:34:17.808055+00:00
-- url     : https://prove2.me/submissions/8b7621e7-28a8-4b32-a6d5-ea080f2cd270

import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_IsPairingValueAddRight
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemSpan
import Theorems.Thm_ReciprocityTheory_PGsh_OAdj_pairing_iff
import Theorems.Thm_ReciprocityTheory_PGsh_ht_ext
import Theorems.Thm_ReciprocityTheory_PGsh_BX_pairing_sw


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
open ReciprocityTheory.PGsh.OAdj
variable {B : BX R₀} {O : LAlg R₀} (A : OAdj B O) {R : LAlg R₀} (s : LHom O R)
namespace ReciprocityTheory.PGsh.OAdj
theorem _root_.solution (Dp : DualPair R) (N : ℕ) (y : B.G R) (h : B.gg →ₗ[R₀] (R : Type u))
    (δ : B.gg →ₗ[R₀] B.gg ⊗[R₀] (R : Type u)) (hy : N • y = 0) (hH : B.IsHeight Dp N y h)
    (hδ : ∀ v, A.ab.f (Dp.σ.comp s) (B.tg Dp.π Dp.sqZero (v ⊗ₜ Dp.ηk)) =
      B.tg Dp.π Dp.sqZero (LinearMap.lTensor B.gg Dp.ηmap (δ v))) :
    B.IsHeight Dp N (A.a.f s y) (hext B h ∘ₗ δ) := by
  intro v
  obtain ⟨z, hz, ez⟩ := ht_ext B Dp N y h hy hH (δ v)
  rw [← hδ v] at hz
  obtain ⟨z0, hz0, -⟩ := hH v
  obtain ⟨hX, hY, -⟩ := hz0
  have k1 := B.pairing_sw N _ _ z hz
  have k2 := (A.pairing_iff (Dp.σ.comp s) N _ _ z⁻¹ hY hX).2 k1
  have k3 := B.pairing_sw N _ _ _ k2
  rw [inv_inv, A.a.nat] at k3
  exact ⟨z, k3, by rw [ez]; rfl⟩
end ReciprocityTheory.PGsh.OAdj
