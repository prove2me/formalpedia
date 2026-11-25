-- Prove2me | solution 1 for P2M_RH_P2M_ReciprocityTheory_PGsh_DualPair___comp___27dea36124af_608b5bca99eb579b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:51:30.681371+00:00
-- url     : https://prove2.me/submissions/e28d3d8b-c11e-497b-a139-2b1fe9ee5eae

import Definitions.Def_ReciprocityTheory_DualLattices_ModuliPointsState
import Definitions.Def_ReciprocityTheory_DualLattices_NilSurjOfSqZero
import Theorems.Thm_P2M_RH_P2M_ReciprocityTheory_PGsh_LHom_ext__04d8c2f369fc_bb2327b66623d504

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
theorem _root_.solution : Dp.π.comp Dp.σ = LHom.id R := LHom.ext' (fun r => Dp.sect r)
end ReciprocityTheory.PGsh.DualPair
