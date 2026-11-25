-- Prove2me | solution 1 for P2M_ReciprocityTheory_PGsh_DualPair___ker_0eced12ea04a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:01:44.571728+00:00
-- url     : https://prove2.me/submissions/5260ed45-f7f8-4819-8e8f-5726097745a8

import Definitions.Def_ReciprocityTheory_DualLattices_ModuliPointsState
import Definitions.Def_ReciprocityTheory_DualLattices_IsFibreSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.PGsh
universe u
variable {R₀ : Type u} [CommRing R₀]
open ReciprocityTheory.PGsh.DualPair
variable {R : LAlg R₀} (Dp : DualPair R)
namespace ReciprocityTheory.PGsh.DualPair
theorem _root_.solution : Dp.η ∈ RingHom.ker Dp.π.1 := by
  rw [Dp.ker_eq]; exact Ideal.subset_span (Set.mem_singleton _)
end ReciprocityTheory.PGsh.DualPair
