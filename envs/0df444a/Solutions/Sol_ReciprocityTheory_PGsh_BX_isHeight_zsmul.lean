-- Prove2me | solution 1 for ReciprocityTheory.PGsh.BX.isHeight_zsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:46:13.691982+00:00
-- url     : https://prove2.me/submissions/a60de860-d0ed-44ba-8697-255af70c35fa

import Definitions.Def_ReciprocityTheory_DualLattices_HtLinStatement
import Definitions.Def_ReciprocityTheory_DualLattices_HeightFunctionalStatementOfPairingProperties
import Definitions.Def_ReciprocityTheory_DualLattices_IsHeightUnique
import Theorems.Thm_ReciprocityTheory_PGsh_BX_isHeight_add
import Theorems.Thm_ReciprocityTheory_PGsh_BX_isHeight_zero
import Theorems.Thm_ReciprocityTheory_PGsh_BX_isHeight_neg

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
theorem _root_.solution (hB1 : PairingPropertiesStatement B) {R : LAlg R₀} (Dp : DualPair R) (N : ℕ)
    (hN : (N : (R : Type u)) = 0) {y : B.G R} (hy : N • y = 0) {h : B.gg →ₗ[R₀] (R : Type u)}
    (H : B.IsHeight Dp N y h) (k : ℤ) : B.IsHeight Dp N (k • y) (k • h) := by
  have hnat : ∀ m : ℕ, B.IsHeight Dp N (m • y) (m • h) := by
    intro m
    induction m with
    | zero => simpa using B.isHeight_zero hB1 Dp N hN
    | succ m ih => rw [succ_nsmul, succ_nsmul]; exact B.isHeight_add hB1 Dp N hN ih H
  rcases k with m | m
  · simpa using hnat m
  · have hm : N • ((m + 1) • y) = 0 := by rw [smul_comm, hy, smul_zero]
    have := B.isHeight_neg hB1 Dp N hN hm (hnat (m + 1))
    simpa [negSucc_zsmul] using this
end ReciprocityTheory.PGsh.BX
