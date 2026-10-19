-- Prove2me | solution 1 for PermanentRollout.permanent_circuit_gradient_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:11.481307+00:00
-- url     : https://prove2.me/submissions/c15d17f3-f107-4679-b5b1-e3ae883e3164

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_sliced_gradient_logarithmic_bound_of_fiber_cardinalities
import Theorems.Thm_PermanentRollout_exists_sourceTreeBlock_slicedGradient
import Theorems.Thm_PermanentRollout_exists_source_floor_blockTree
import Theorems.Thm_PermanentRollout_sourceTreeBlock_slicedGradient_homogeneousFiberDegree_le_two_pow

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section
namespace PermanentRollout
theorem _root_.solution
    {n d : ℕ} (hd : 3 ≤ d)
    (hn : 6 * blockWidth d ≤ n)
    (hscale : 4 * powerSumParameter d ≤
      blockWidth d * blockColumns n d)
    (circuit : ArithmeticCircuit (Fin n × Fin n))
    (hpermanent : circuit.polynomial = permanent n) :
    (sliceRank n d : ℝ) * Real.logb 2 ((d : ℝ) - 1) ≤
      3 * (circuit.size : ℝ) := by
  obtain ⟨tree, hnodup, hleaves⟩ :=
    exists_source_floor_blockTree hd hn
  obtain ⟨W, A, _, hhomogeneous, hzero⟩ :=
    exists_sourceTreeBlock_slicedGradient
      hd hn hscale tree hnodup hleaves
  have hpower :=
    sourceTreeBlock_slicedGradient_homogeneousFiberDegree_le_two_pow
      hd hn circuit hpermanent tree hnodup hleaves W A
      hhomogeneous hzero
  simpa using
    (sliced_gradient_logarithmic_bound_of_fiber_cardinalities
      (k := sliceRank n d) (d := d) (q := 3 * circuit.size)
      (cardinality := (d - 1) ^ sliceRank n d)
      (by omega) (le_refl _) hpower)
end PermanentRollout
