-- Prove2me | solution 1 for ReciprocityTheory.PGsh.BX.isHeight_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:31:11.696299+00:00
-- url     : https://prove2.me/submissions/44076703-f806-40b4-b08a-4f4a7dfe90f2

import Definitions.Def_ReciprocityTheory_DualLattices_HtLinStatement
import Definitions.Def_ReciprocityTheory_DualLattices_HeightFunctionalStatementOfPairingProperties
import Definitions.Def_ReciprocityTheory_DualLattices_IsHeightUnique
import Theorems.Thm_ReciprocityTheory_PGsh_BX_isHeight_unique
import Theorems.Thm_ReciprocityTheory_PGsh_BX_isHeight_exists
import Theorems.Thm_ReciprocityTheory_PGsh_BX_isHeight_add

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
    (hN : (N : (R : Type u)) = 0) : B.IsHeight Dp N 0 0 := by
  obtain ⟨h, hh⟩ := B.isHeight_exists hB1 Dp N hN 0 (smul_zero N)
  have h2 := B.isHeight_add hB1 Dp N hN hh hh
  rw [add_zero] at h2
  have h3 := B.isHeight_unique hB1 Dp N hN 0 (smul_zero N) _ _ hh h2
  have h4 : h = 0 := by
    have := congrArg (fun k => k - h) h3
    simpa using this.symm
  rwa [h4] at hh
end ReciprocityTheory.PGsh.BX
