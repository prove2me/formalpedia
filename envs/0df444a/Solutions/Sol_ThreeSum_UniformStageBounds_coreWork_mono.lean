-- Prove2me | solution 1 for ThreeSum.UniformStageBounds.coreWork_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:49:23.649464+00:00
-- url     : https://prove2.me/submissions/9ee83184-61ee-45a2-9703-36b5b26c4686

import Definitions.Def_Submission_ThreeSum_StageBounds
import Definitions.Def_Submission_ThreeSum_UniformStageBounds

set_option autoImplicit false
open ThreeSum ThreeSum.UniformStageBounds
open Filter Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.TrimScales
  ThreeSum.BandScales ThreeSum.Switch ThreeSum.CostLedger ThreeSum.HierarchyScales
  ThreeSum.MassScales ThreeSum.StageBounds
open scoped Topology
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
namespace ThreeSum.UniformStageBounds
theorem _root_.solution {W W' H H' : ℕ → ℕ} {n : ℕ}
    (hW : W n ≤ W' n) (hH : H n ≤ H' n) : coreWork W H n ≤ coreWork W' H' n := by
  have hi := Nat.mul_le_mul_right (queryTerms n 0) hW
  have ha := Nat.mul_le_mul_right (allQueryTerms n)
    (Nat.mul_le_mul_right (microPartitions n) (Nat.mul_le_mul_right (representationBound n) hH))
  have ht := Nat.mul_le_mul_right (terminalChoices n)
    (Nat.mul_le_mul_right (representationBound n) (Nat.mul_le_mul_left 2 hH))
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.le_refl _) hi) ha) ht
end ThreeSum.UniformStageBounds
