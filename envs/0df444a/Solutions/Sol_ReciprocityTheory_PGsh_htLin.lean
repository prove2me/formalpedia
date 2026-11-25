-- Prove2me | solution 1 for ReciprocityTheory.PGsh.htLin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:56:31.52464+00:00
-- url     : https://prove2.me/submissions/0d3e961b-e36e-4930-b1c7-24912ae01c5a

import Definitions.Def_ReciprocityTheory_DualLattices_ExistsLimTensor
import Definitions.Def_ReciprocityTheory_DualLattices_CharR
import Theorems.Thm_ReciprocityTheory_PGsh_ATower_char_R
import Theorems.Thm_ReciprocityTheory_PGsh_BX_isHeight_sum
import Theorems.Thm_ReciprocityTheory_PGsh_BX_isHeight_zsmul


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
theorem _root_.solution (B : BX R₀) (hB1 : PairingPropertiesStatement B) {p : ℕ} (Tw : ATower R₀ p) (Dp : ∀ n, DualPair (Tw.R n)) :
    HtLinStatement B Tw Dp := by
  intro ι _ τ ht a α hτ hH hα n
  have hN := Tw.char_R n
  have hy : ∀ i, (p ^ (n + 1)) • B.map (Tw.q n) (τ i n) = 0 := fun i => by
    rw [← map_nsmul, hτ i n, map_zero]
  have hlin : (Tw.q n).1.toLinearMap ∘ₗ ∑ i, α i • ht i =
      ∑ i, a i n • ((Tw.q n).1.toLinearMap ∘ₗ ht i) := by
    ext v
    simp [LinearMap.sum_apply, map_sum, map_mul, hα, zsmul_eq_mul]
  rw [map_sum, hlin]
  simp only [map_zsmul]
  exact BX.isHeight_sum (B := B) hB1 (Dp n) (p ^ (n + 1)) hN Finset.univ
    (fun i => a i n • B.map (Tw.q n) (τ i n)) (fun i => by rw [smul_comm, hy i, smul_zero])
    (fun i => a i n • ((Tw.q n).1.toLinearMap ∘ₗ ht i))
    (fun i => BX.isHeight_zsmul (B := B) hB1 (Dp n) (p ^ (n + 1)) hN (hy i) (hH i n) (a i n))
end ReciprocityTheory.PGsh
