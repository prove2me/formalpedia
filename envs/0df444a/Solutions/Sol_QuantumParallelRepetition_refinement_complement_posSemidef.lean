-- Prove2me | solution 1 for QuantumParallelRepetition.refinement_complement_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:14.37599+00:00
-- url     : https://prove2.me/submissions/2e7f0e38-2cf5-4e34-969f-dc32894b291f

import Mathlib
import Definitions.Def_QuantumParallelRepetition

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
namespace QuantumParallelRepetition
theorem _root_.solution
    {ι d : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype d] [DecidableEq d]
    (effect : ι → Matrix d d ℂ)
    (hpositive : ∀ a, (effect a).PosSemidef)
    (a : ι) :
    ((∑ b : ι, effect b) - effect a).PosSemidef := by
  have herase : (∑ b ∈ Finset.univ.erase a, effect b).PosSemidef := by
    apply Matrix.posSemidef_sum (Finset.univ.erase a)
    intro c _
    exact hpositive c
  have hsum : effect a +
      (∑ b ∈ Finset.univ.erase a, effect b) =
      ∑ b : ι, effect b := by
    simp
  rw [← hsum, add_sub_cancel_left]
  exact herase
end QuantumParallelRepetition
