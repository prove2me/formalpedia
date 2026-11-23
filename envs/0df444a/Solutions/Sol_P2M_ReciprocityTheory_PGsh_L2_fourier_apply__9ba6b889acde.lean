-- Prove2me | solution 1 for P2M_ReciprocityTheory_PGsh_L2_fourier_apply__9ba6b889acde
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:22:36.61183+00:00
-- url     : https://prove2.me/submissions/8c494c72-dae9-4681-b17a-4dcf38e33d8b

import Definitions.Def_ReciprocityTheory_DualLattices_ValuationDetEqOfSpanEq
import Definitions.Def_ReciprocityTheory_DualLattices_ValuationFourierLeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
namespace ReciprocityTheory.PGsh.L2
theorem _root_.solution {X H : Type} [Fintype X] (e : H → X → C) (u : X → C) (h : H) :
    fourier (R := R) e u h = ∑ a, u a * e h a := rfl
end ReciprocityTheory.PGsh.L2
