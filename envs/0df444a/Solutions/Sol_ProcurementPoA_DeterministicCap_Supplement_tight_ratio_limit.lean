-- Prove2me | solution 1 for ProcurementPoA.DeterministicCap.Supplement.tight_ratio_limit
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:33:24.601315+00:00
-- url     : https://prove2.me/submissions/647dfe75-e9f5-4619-aeab-32b89b97aa93

import Mathlib
import Definitions.Def_ProcurementPoA_DeterministicCap_CapFormula

open Filter Topology
open ProcurementPoA.DeterministicCap

/-- The real limit in Remark 4.2 after the affine transformation from values to costs. -/
theorem solution
    (L U : ℝ) (hL : 0 < L) (hLU : L ≤ U)
    (opt wel : ℕ → ℝ)
    (hopt : Filter.Tendsto opt Filter.atTop (𝓝 1))
    (hwel : Filter.Tendsto wel Filter.atTop (𝓝 (1 - ProcurementPoA.DeterministicCap.epsilon))) :
    Filter.Tendsto (fun k => (U - (U - L) * wel k) / (U - (U - L) * opt k))
      Filter.atTop (𝓝 (1 + ProcurementPoA.DeterministicCap.epsilon * (U / L - 1))) := by
  have hden : Tendsto (fun k => U - (U - L) * opt k) atTop
      (𝓝 (U - (U - L) * 1)) := (hopt.const_mul (U - L)).const_sub U
  have hnum : Tendsto (fun k => U - (U - L) * wel k) atTop
      (𝓝 (U - (U - L) * (1 - epsilon))) := (hwel.const_mul (U - L)).const_sub U
  have hLden : U - (U - L) * 1 ≠ 0 := by linarith
  have heq : (U - (U - L) * (1 - epsilon)) / (U - (U - L) * 1) =
      1 + epsilon * (U / L - 1) := by
    rw [div_eq_iff hLden]
    field_simp [hL.ne']
    ring
  rw [← heq]
  exact hnum.div hden hLden
