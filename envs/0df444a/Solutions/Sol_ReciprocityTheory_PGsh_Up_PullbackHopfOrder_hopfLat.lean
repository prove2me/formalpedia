-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.PullbackHopfOrder.hopfLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:31:23.307281+00:00
-- url     : https://prove2.me/submissions/55d09673-3e81-4359-8ffa-1707bdc3d410

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
theorem _root_.solution {K : Type} {_ : AddCommGroup K} {_ : Fintype K} {_ : DecidableEq K}
    (A : HopfOrder (C := C) R K) : IsLat R A.carrier := A.lat
end ReciprocityTheory.PGsh.Up.PullbackHopfOrder
