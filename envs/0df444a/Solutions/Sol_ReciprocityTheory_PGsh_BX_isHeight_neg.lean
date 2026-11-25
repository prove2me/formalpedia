-- Prove2me | solution 1 for ReciprocityTheory.PGsh.BX.isHeight_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:37:37.834583+00:00
-- url     : https://prove2.me/submissions/eca113c8-26d9-4b39-97ae-fb57fce373d8

import Definitions.Def_ReciprocityTheory_DualLattices_HtLinStatement
import Definitions.Def_ReciprocityTheory_DualLattices_HeightFunctionalStatementOfPairingProperties
import Definitions.Def_ReciprocityTheory_DualLattices_IsHeightUnique
import Theorems.Thm_ReciprocityTheory_PGsh_BX_isHeight_unique
import Theorems.Thm_ReciprocityTheory_PGsh_BX_isHeight_exists
import Theorems.Thm_ReciprocityTheory_PGsh_BX_isHeight_add
import Theorems.Thm_ReciprocityTheory_PGsh_BX_isHeight_zero

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
    (H : B.IsHeight Dp N y h) : B.IsHeight Dp N (-y) (-h) := by
  obtain ⟨h', hh'⟩ := B.isHeight_exists hB1 Dp N hN (-y) (by rw [smul_neg, hy, neg_zero])
  have h2 := B.isHeight_add hB1 Dp N hN H hh'
  rw [add_neg_cancel] at h2
  have h3 := B.isHeight_unique hB1 Dp N hN 0 (smul_zero N) _ _ h2 (B.isHeight_zero hB1 Dp N hN)
  have h4 : h' = -h := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact h3
  rwa [h4] at hh'
end ReciprocityTheory.PGsh.BX
