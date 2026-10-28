-- Prove2me | solution 1 for Ultrafilter.exists_tendsto_of_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T00:31:21.923192+00:00
-- url     : https://prove2.me/submissions/3b323391-50b7-4d9a-8bfb-e432ba0a8c9d

import Mathlib

open InnerProductSpace
open Filter Topology

-- carved verbatim out of submission 2cce955e-db83-4e7c-bbea-5f4e097d3ccf, lines 12-19


theorem solution {ι : Type*} (f : ι → ℝ) (M : ℝ) (hM : ∀ k, |f k| ≤ M) (U : Ultrafilter ι) :
    ∃ a, Tendsto f U (𝓝 a) := by
  have hc : IsCompact (Set.Icc (-M) M) := isCompact_Icc
  obtain ⟨a, -, ha⟩ := hc.ultrafilter_le_nhds (U.map f) (by
    rw [Filter.le_principal_iff, Ultrafilter.coe_map, Filter.mem_map]
    exact Filter.univ_mem' (fun k => abs_le.1 (hM k)))
  exact ⟨a, ha⟩
