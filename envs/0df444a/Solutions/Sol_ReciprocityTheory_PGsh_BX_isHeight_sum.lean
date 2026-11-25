-- Prove2me | solution 1 for ReciprocityTheory.PGsh.BX.isHeight_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:41:39.486723+00:00
-- url     : https://prove2.me/submissions/35918966-7bbc-48d3-b522-252de91b9525

import Definitions.Def_ReciprocityTheory_DualLattices_HtLinStatement
import Definitions.Def_ReciprocityTheory_DualLattices_HeightFunctionalStatementOfPairingProperties
import Definitions.Def_ReciprocityTheory_DualLattices_IsHeightUnique
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
    (hN : (N : (R : Type u)) = 0) {ι : Type} (s : Finset ι) (y : ι → B.G R) (hy : ∀ i, N • y i = 0)
    (h : ι → B.gg →ₗ[R₀] (R : Type u)) (H : ∀ i, B.IsHeight Dp N (y i) (h i)) :
    B.IsHeight Dp N (∑ i ∈ s, y i) (∑ i ∈ s, h i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using B.isHeight_zero hB1 Dp N hN
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact B.isHeight_add hB1 Dp N hN (H a) ih
end ReciprocityTheory.PGsh.BX
