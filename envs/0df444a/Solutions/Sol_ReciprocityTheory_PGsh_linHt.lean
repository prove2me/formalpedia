-- Prove2me | solution 1 for ReciprocityTheory.PGsh.linHt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:46:54.449852+00:00
-- url     : https://prove2.me/submissions/2128928d-9599-499f-973d-5d887dc18cfa

import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_IsPairingValueAddRight
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemSpan
import Theorems.Thm_ReciprocityTheory_PGsh_OAdj_ht_a

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
theorem _root_.solution (B : BX R₀) (O : LAlg R₀) : LinHtStatement B O :=
  fun A _ s Dp N y h δ hy hH hδ => A.ht_a s Dp N y h δ hy hH hδ
end ReciprocityTheory.PGsh
