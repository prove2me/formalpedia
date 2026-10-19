-- Prove2me | solution 1 for SpherePacking.tendsto_log_harmonicDimension_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:35.361684+00:00
-- url     : https://prove2.me/submissions/88f86562-eee6-4794-8d8a-f4510f760cfc

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_SpherePacking_harmonicEntropyBase_pos
import Theorems.Thm_SpherePacking_harmonicDimension_choose_bounds
import Theorems.Thm_SpherePacking_tendsto_log_harmonicEntropyBase_div
import Theorems.Thm_SpherePacking_tendsto_log_two_mul_harmonicEntropyBase_div

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
open SpherePacking
noncomputable section
set_option autoImplicit false
open Filter Real
open scoped Nat Topology
namespace SpherePacking
theorem _root_.solution
    (u : ℝ) (hu : 0 < u)
    (N : ℕ → ℕ)
    (hN : Tendsto N atTop atTop)
    (hNratio : Tendsto (fun n : ℕ => (N n : ℝ) / (n : ℝ))
      atTop (nhds 1)) :
    Tendsto
      (fun n : ℕ =>
        Real.log
          (Gegenbauer.harmonicDimension (N n) ⌊u * (n : ℝ)⌋₊ : ℝ) /
          (n : ℝ))
      atTop (nhds ((1 + u) * Real.log (1 + u) - u * Real.log u)) := by
  have hlower := tendsto_log_harmonicEntropyBase_div u hu N hN hNratio
  have hupper := tendsto_log_two_mul_harmonicEntropyBase_div u hu N hN hNratio
  have hbounds :
      ∀ᶠ n : ℕ in atTop,
        harmonicEntropyBase u N n ≤
            Gegenbauer.harmonicDimension (N n) ⌊u * (n : ℝ)⌋₊ ∧
          Gegenbauer.harmonicDimension (N n) ⌊u * (n : ℝ)⌋₊ ≤
            2 * harmonicEntropyBase u N n := by
    filter_upwards
      [hN.eventually (eventually_ge_atTop 2),
       (tendsto_nat_floor_mul_atTop u hu).eventually
         (eventually_ge_atTop 1)] with n hn hk
    have hb := harmonicDimension_choose_bounds hn hk
    have hindex :
        N n + ⌊u * (n : ℝ)⌋₊ - 2 =
          ⌊u * (n : ℝ)⌋₊ + (N n - 2) := by
      omega
    simpa only [harmonicEntropyBase, hindex] using hb
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · filter_upwards [hbounds] with n hn
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    apply Real.log_le_log
    · exact_mod_cast harmonicEntropyBase_pos u N n
    · exact_mod_cast hn.1
  · filter_upwards [hbounds] with n hn
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    apply Real.log_le_log
    · have hpos :
          0 < Gegenbauer.harmonicDimension (N n) ⌊u * (n : ℝ)⌋₊ :=
        lt_of_lt_of_le (harmonicEntropyBase_pos u N n) hn.1
      exact_mod_cast hpos
    · exact_mod_cast hn.2
end SpherePacking
