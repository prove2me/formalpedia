-- Prove2me | solution 1 for P2M_ReciprocityTheory_PGsh_DualPair_mr___4f4cf4efc828
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:01:51.238856+00:00
-- url     : https://prove2.me/submissions/36ac0069-ae1b-493b-b867-508d619a5d1f

import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_IsPairingValueAddRight
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemSpan
import Theorems.Thm_ReciprocityTheory_PGsh_DualPair_mr_apply

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
open ReciprocityTheory.PGsh.DualPair
variable {R : LAlg R₀} (Dp : DualPair R)
namespace ReciprocityTheory.PGsh.DualPair
theorem _root_.solution (r : (R : Type u)) (d : (Dp.D : Type u)) : Dp.π.1 ((Dp.mr r).1 d) = Dp.π.1 d := by
  simp [mr_apply, Dp.sect]
end ReciprocityTheory.PGsh.DualPair
