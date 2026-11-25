-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.PullbackHopfOrder.pullHopf_carrier
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:36:54.815224+00:00
-- url     : https://prove2.me/submissions/709a3214-8acd-467f-87f0-3e727509f6d3

import Definitions.Def_ReciprocityTheory_DualLattices_MemDualLat
import Definitions.Def_ReciprocityTheory_DualLattices_MapTensorSpan
import Definitions.Def_ReciprocityTheory_DualLattices_ExistsMatOfEquiv

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
theorem _root_.solution {N X : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
    [AddCommGroup X] [Fintype X] [DecidableEq X] (ψ : X →+ N) (AA : HopfOrder (C := C) R N)
    (hlat : IsLat R (AA.carrier.map (LinearMap.funLeft R C ψ))) :
    (pullHopf ψ AA hlat).carrier = AA.carrier.map (LinearMap.funLeft R C ψ) := rfl
end ReciprocityTheory.PGsh.Up.PullbackHopfOrder
