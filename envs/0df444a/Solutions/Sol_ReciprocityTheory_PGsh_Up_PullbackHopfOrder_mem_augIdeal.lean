-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.PullbackHopfOrder.mem_augIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:35:47.411098+00:00
-- url     : https://prove2.me/submissions/5a82438d-a8fe-48dd-91cf-d6afc091da0d

import Definitions.Def_ReciprocityTheory_DualLattices_CotangentSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_MemAugIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.PullbackHopfOrder
open ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
namespace ReciprocityTheory.PGsh.Up.PullbackHopfOrder
theorem _root_.solution {X : Type} [AddCommGroup X] {M : Submodule R (X → C)} {f : X → C} :
    f ∈ augIdeal M ↔ f ∈ M ∧ f 0 = 0 := by
  exact Iff.rfl
end ReciprocityTheory.PGsh.Up.PullbackHopfOrder
