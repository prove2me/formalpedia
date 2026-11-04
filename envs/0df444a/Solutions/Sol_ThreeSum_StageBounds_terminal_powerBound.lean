-- Prove2me | solution 1 for ThreeSum.StageBounds.terminal_powerBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:03:16.417802+00:00
-- url     : https://prove2.me/submissions/dfab7e04-f092-45cb-997e-5fb0250a3d12

import Definitions.Def_Submission_ThreeSum_MassScales
import Definitions.Def_Submission_ThreeSum_StageBounds
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_of_rate
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_const
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_mul
import Theorems.Thm_ThreeSum_StageBounds_false_powerBound
import Definitions.Def_WeightedCache3SUM_Alias_7657fba77cd7b9c1
import Definitions.Def_WeightedCache3SUM_Alias_dc2f19a97a662b74


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
theorem _root_.solution {H P H1 : ℕ → ℕ} (k : ℕ)
    (hscore : ∀ᶠ n : ℕ in atTop, P n * H n ≤ scoreLoss k n * H1 n)
    (hinit : ∀ᶠ n : ℕ in atTop, H1 n ≤ candidateCount n * rawTripleBound n)
    (hmod : ∀ᶠ n : ℕ in atTop, radix n ≤ primeLoss radix n * P n) :
    PowerBound (terminalCount H)
      (2 - epsilon * (terminalFraction - 1 / 2 - bandShift - kappa)) := by
  have hh := (((PowerBound.const 2).mul (false_powerBound k hscore hinit hmod)).mul
    (PowerBound.of_rate representationBound_log_rate)).mul (PowerBound.of_rate terminalChoices_log_rate)
  have heq : ((0 : ℝ) + (2 - (1 / 2 - bandShift) / 5) + kappa / 5) +
      (1 - terminalFraction) / 5 =
      2 - epsilon * (terminalFraction - 1 / 2 - bandShift - kappa) := by unfold epsilon; ring
  rw [heq] at hh
  exact hh
end ThreeSum.StageBounds
