-- Prove2me | solution 1 for ReciprocityTheory.PGsh.BX.isHeight_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:21:02.751802+00:00
-- url     : https://prove2.me/submissions/6546ff5b-d638-4361-928b-6fbf874a8786

import Definitions.Def_ReciprocityTheory_DualLattices_HtLinStatement
import Definitions.Def_ReciprocityTheory_DualLattices_HeightFunctionalStatementOfPairingProperties
import Definitions.Def_ReciprocityTheory_DualLattices_IsHeightUnique
import Theorems.Thm_ReciprocityTheory_PGsh_heightFunctionalStatement_of_pairingProperties


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
    (hN : (N : (R : Type u)) = 0) {y y' : B.G R} {h h' : B.gg →ₗ[R₀] (R : Type u)}
    (H : B.IsHeight Dp N y h) (H' : B.IsHeight Dp N y' h') : B.IsHeight Dp N (y + y') (h + h') :=
  (heightFunctionalStatement_of_pairingProperties B hB1 R Dp N hN).2.2 y y' h h' H H'
end ReciprocityTheory.PGsh.BX
