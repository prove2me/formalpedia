-- Prove2me | solution 1 for ReciprocityTheory.PGsh.L2.det_map_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:17:38.044798+00:00
-- url     : https://prove2.me/submissions/ad8e1ad4-2a6e-46e2-a90c-60e76b11737b

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_IsUnitDetOfSpanEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}
namespace ReciprocityTheory.PGsh.L2
theorem _root_.solution {X : Type} [Fintype X] [DecidableEq X] (M : Matrix X X R) :
    (M.map (algebraMap R C)).det = algebraMap R C M.det := by
  rw [RingHom.map_det]
  rfl
end ReciprocityTheory.PGsh.L2
