-- Prove2me | solution 1 for ReciprocityTheory.PGsh.L2.SecondCohomologyLattice.apply_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:31:24.864904+00:00
-- url     : https://prove2.me/submissions/d2c392f1-ca53-44ee-8d8f-1536100e3e89

import Definitions.Def_ReciprocityTheory_DualLattices_TensorSpan
import Definitions.Def_ReciprocityTheory_DualLattices_MapTensorSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.L2.SecondCohomologyLattice
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
namespace ReciprocityTheory.PGsh.L2.SecondCohomologyLattice
theorem _root_.solution {X : Type} [Fintype X] [DecidableEq X] (E : (X → C) →ₗ[C] (X → C))
    (f : X → C) (y : X) :
    E f y = ∑ a, f a * E (fun j => if a = j then 1 else 0) y := by
  have hf : f = ∑ a, f a • (fun j => if a = j then (1 : C) else 0) := by
    funext j
    simp [Finset.sum_apply]
  conv_lhs => rw [hf]
  rw [map_sum, Finset.sum_apply]
  simp [map_smul]
end ReciprocityTheory.PGsh.L2.SecondCohomologyLattice
