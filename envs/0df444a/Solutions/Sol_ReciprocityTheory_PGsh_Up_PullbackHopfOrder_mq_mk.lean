-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.PullbackHopfOrder.mq_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:44:00.727643+00:00
-- url     : https://prove2.me/submissions/42b575bd-596f-49ca-8e9f-e494cc7e89fe

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
theorem _root_.solution (q : ℕ) {a b : ℕ} (G : Matrix (Fin a) (Fin b) R) (x : Fin b → R) :
    mq q G (Submodule.Quotient.mk x) = Submodule.Quotient.mk (G *ᵥ x) := rfl
end ReciprocityTheory.PGsh.Up.PullbackHopfOrder
