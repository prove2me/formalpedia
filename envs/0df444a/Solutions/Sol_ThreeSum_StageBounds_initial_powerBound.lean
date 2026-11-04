-- Prove2me | solution 1 for ThreeSum.StageBounds.initial_powerBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:55:36.591734+00:00
-- url     : https://prove2.me/submissions/02318f29-50f6-4996-bfee-cf2a46c75c7b

import Definitions.Def_Submission_ThreeSum_MassScales
import Definitions.Def_Submission_ThreeSum_StageBounds
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_mul
import Theorems.Thm_ThreeSum_StageBounds_wanted_powerBound
import Definitions.Def_WeightedCache3SUM_Alias_6f49b526313dc28e


set_option autoImplicit false
open ThreeSum ThreeSum.StageBounds
open Filter Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.TrimScales
  ThreeSum.BandScales ThreeSum.Switch ThreeSum.CostLedger ThreeSum.HierarchyScales
  ThreeSum.MassScales
open scoped Topology
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
namespace ThreeSum.StageBounds
theorem _root_.solution {W : ℕ → ℕ}
    (hW : ∀ᶠ n : ℕ in atTop, W n * radix n ≤ wantedNumerator n) :
    PowerBound (initialCount W) (2 - epsilon * (1 / 2 + bandShift - entropy initialTheta)) := by
  have hQ : PowerBound (fun n => queryTerms n 0) (entropy initialTheta / 5) :=
    fun _ hd => initial_query_eventually_le hd
  have hh := (wanted_powerBound hW).mul hQ
  have heq : (2 - (1 / 2 + bandShift) / 5) + entropy initialTheta / 5 =
      2 - epsilon * (1 / 2 + bandShift - entropy initialTheta) := by unfold epsilon; ring
  rw [heq] at hh
  exact hh
end ThreeSum.StageBounds
