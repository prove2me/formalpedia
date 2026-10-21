-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P07.lemma1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T10:12:36.906272+00:00
-- url     : https://prove2.me/submissions/b2afad42-6654-4cd2-9fe0-c9239356cb42

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P07
noncomputable section

open Filter

open scoped NNReal ENNReal BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P07

open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Frontier30.P05 (EnergySpectrum groundEnergy)

theorem solution (f : ℝ → ℝ) (hf : ConcaveOn ℝ (Set.Ici 0) f)
    (hnonneg : ∀ u ∈ Set.Ici (0 : ℝ), 0 ≤ f u)
    (x y z : ℝ) (hx : 0 < x) (hxy : x < y) (hz : 0 ≤ z) :
    x * f (z / x) ≤ y * f (z / y) := by
  have hy : 0 < y := hx.trans hxy
  have ha : 0 ≤ x / y := div_nonneg hx.le hy.le
  have hb : 0 ≤ 1 - x / y := by rw [sub_nonneg, div_le_one hy]; exact hxy.le
  have key := hf.2 (x := z / x) (y := 0) (Set.mem_Ici.mpr (div_nonneg hz hx.le))
    (Set.mem_Ici.mpr le_rfl) ha hb (by ring)
  have e : (x / y) * (z / x) + (1 - x / y) * (0:ℝ) = z / y := by
    rw [mul_zero, add_zero]; field_simp
  simp only [smul_eq_mul] at key
  rw [e] at key
  have h0 := hnonneg 0 (Set.mem_Ici.mpr le_rfl)
  have : x / y * f (z / x) ≤ f (z / y) := by nlinarith
  have := mul_le_mul_of_nonneg_left this hy.le
  rw [← mul_assoc, mul_div_cancel₀ _ hy.ne'] at this
  exact this

end
