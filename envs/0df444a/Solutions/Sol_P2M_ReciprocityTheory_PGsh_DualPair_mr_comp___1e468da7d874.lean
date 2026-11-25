-- Prove2me | solution 1 for P2M_ReciprocityTheory_PGsh_DualPair_mr_comp___1e468da7d874
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:59:15.231093+00:00
-- url     : https://prove2.me/submissions/0328856b-4be1-4129-a9ca-e4f62018c5b9

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
theorem _root_.solution (r : (R : Type u)) : (Dp.mr r).comp Dp.σ = Dp.σ :=
  Subtype.ext (AlgHom.ext fun t => by
    show (Dp.mr r).1 (Dp.σ.1 t) = Dp.σ.1 t
    simp [mr_apply, Dp.sect])
end ReciprocityTheory.PGsh.DualPair
