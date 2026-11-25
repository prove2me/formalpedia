-- Prove2me | solution 1 for ReciprocityTheory.PGsh.ht_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:20:26.662049+00:00
-- url     : https://prove2.me/submissions/3c07aaf3-f06a-4060-915d-18a62ed96eda

import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_IsPairingValueAddRight
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemSpan
import Theorems.Thm_P2M_RH_P2M_ReciprocityTheory_PGsh_DualPair_____9b8197f73975_35ac38284c5cda63
import Theorems.Thm_ReciprocityTheory_PGsh_DualPair_mr_apply
import Theorems.Thm_P2M_ReciprocityTheory_PGsh_DualPair_mr_comp___1e468da7d874
import Theorems.Thm_P2M_ReciprocityTheory_PGsh_DualPair_mr____648a9fda1d75
import Theorems.Thm_ReciprocityTheory_PGsh_DualPair_mr_ker
import Theorems.Thm_ReciprocityTheory_PGsh_hext_tmul
import Theorems.Thm_ReciprocityTheory_PGsh_BX_isPairingValue_add_left
import Theorems.Thm_ReciprocityTheory_PGsh_BX_pairing_exists
import Theorems.Thm_ReciprocityTheory_PGsh_BX_pairing_map
import Theorems.Thm_ReciprocityTheory_PGsh_BX_pairing_unique


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
theorem _root_.solution (B : BX R₀) {R : LAlg R₀} (Dp : DualPair R) (N : ℕ) (y : B.G R)
    (h : B.gg →ₗ[R₀] (R : Type u)) (hy : N • y = 0) (hH : B.IsHeight Dp N y h)
    (V : B.gg ⊗[R₀] (R : Type u)) :
    ∃ z : (Dp.D : Type u)ˣ,
      B.IsPairing N (B.tg Dp.π Dp.sqZero (LinearMap.lTensor B.gg Dp.ηmap V)) (B.map Dp.σ y) z ∧
        (z : (Dp.D : Type u)) = 1 + Dp.σ.1 (hext B h V) * Dp.η := by
  induction V using TensorProduct.induction_on with
  | zero =>
    have hY : N • B.map Dp.σ y = 0 := by rw [← map_nsmul, hy, map_zero]
    obtain ⟨z, hz⟩ := B.pairing_exists N (0 : B.G Dp.D) _ (smul_zero N) hY
    have h2 := B.isPairingValue_add_left N 0 0 _ z z hz hz
    rw [add_zero] at h2
    have hzz : z * z = z * 1 := by rw [mul_one]; exact (B.pairing_unique N _ _ _ _ hz h2).symm
    have h1 : z = 1 := mul_left_cancel hzz
    subst h1
    refine ⟨1, by simpa using hz, by simp⟩
  | tmul w r =>
    obtain ⟨z, hz, ez⟩ := hH w
    have k := B.pairing_map (Dp.mr r) N _ _ z hz
    have e1 : B.map (Dp.mr r) (B.tg Dp.π Dp.sqZero (w ⊗ₜ Dp.ηk)) =
        B.tg Dp.π Dp.sqZero (LinearMap.lTensor B.gg Dp.ηmap (w ⊗ₜ r)) := by
      rw [← B.tg_nat Dp.π Dp.π Dp.sqZero Dp.sqZero (Dp.mr r) (Dp.mr_ker r),
        LinearMap.lTensor_tmul, LinearMap.lTensor_tmul]
      congr 2
      exact Subtype.ext (by simp [DualPair.ηk, DualPair.ηmap, DualPair.mr_apply, Dp.π_η, LinearMap.restrict_apply])
    have e2 : B.map (Dp.mr r) (B.map Dp.σ y) = B.map Dp.σ y := by
      rw [← B.map_comp, Dp.mr_comp_σ]
    rw [e1, e2] at k
    refine ⟨_, k, ?_⟩
    simp only [Units.coe_map, MonoidHom.coe_coe]
    rw [ez, map_add, map_one, Dp.mr_ση, hext_tmul, map_mul]
    ring
  | add V V' ihV ihV' =>
    obtain ⟨z, hz, ez⟩ := ihV
    obtain ⟨z', hz', ez'⟩ := ihV'
    refine ⟨z * z', ?_, ?_⟩
    · rw [map_add, map_add]
      exact B.isPairingValue_add_left N _ _ _ z z' hz hz'
    · rw [Units.val_mul, ez, ez', map_add, map_add]
      linear_combination (Dp.σ.1 (hext B h V) * Dp.σ.1 (hext B h V')) * Dp.η_sq
end ReciprocityTheory.PGsh
