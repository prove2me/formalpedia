-- Prove2me | solution 1 for TitiusBode.dermott_geometric_spacing
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-10T19:32:32.862302+00:00
-- url     : https://prove2.me/submissions/6a83fae9-914c-4057-afdd-02696b94ed8f

import Definitions.Def_TitiusBode_Defs
import Mathlib
open Filter Topology
open TitiusBode

theorem solution (T₀ C K : ℝ) (hT₀ : 0 < T₀) (hC : 0 < C) (n : ℕ) :
    dermottPeriod T₀ C (n + 1) / dermottPeriod T₀ C n = C ∧
    K * dermottPeriod T₀ C (n + 1) ^ ((2 : ℝ) / 3) =
      C ^ ((2 : ℝ) / 3) * (K * dermottPeriod T₀ C n ^ ((2 : ℝ) / 3)) := by
  have hpos : 0 < dermottPeriod T₀ C n := by
    unfold dermottPeriod; positivity
  have hsucc : dermottPeriod T₀ C (n + 1) = C * dermottPeriod T₀ C n := by
    unfold dermottPeriod; rw [pow_succ]; ring
  refine ⟨?_, ?_⟩
  · rw [hsucc]; field_simp
  · rw [hsucc, Real.mul_rpow hC.le hpos.le]; ring
