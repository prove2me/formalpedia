-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P19.one_moment_optimum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:03:27.431201+00:00
-- url     : https://prove2.me/submissions/3aeedca8-6b22-4379-88e0-418e71bb7f68

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P19 in
theorem solution (r : ℝ) (hr : 0≤r) (hr1 : r≤1) :
    alpha (![r] : Fin 1 → ℝ) = ENNReal.ofReal (Real.sqrt r) ∧
    discreteFeasible (![r] : Fin 1 → ℝ) (fun _ : Fin 1 => Real.sqrt r) := by
  have hfeas : discreteFeasible (![r] : Fin 1 → ℝ) (fun _ : Fin 1 => Real.sqrt r) := by
    refine ⟨fun _ => ⟨Real.sqrt_nonneg r, Real.sqrt_le_one.mpr hr1⟩, ?_⟩
    intro k
    fin_cases k
    simp [Real.sq_sqrt hr]
  refine ⟨le_antisymm ?_ ?_, hfeas⟩
  · apply sInf_le
    exact ⟨1, fun _ => Real.sqrt r, hfeas, by simp⟩
  · apply le_sInf
    rintro v ⟨N, s, ⟨hs, hmom⟩, rfl⟩
    apply ENNReal.ofReal_le_ofReal
    have h0 : ∀ i ∈ Finset.univ, 0 ≤ s i := fun i _ => (hs i).1
    have hsum : 0 ≤ ∑ i, s i := Finset.sum_nonneg h0
    have hm : ∑ i, s i ^ 2 = r := by simpa using hmom 0
    rw [Real.sqrt_le_left hsum]
    rw [← hm]
    exact Finset.sum_sq_le_sq_sum_of_nonneg h0
