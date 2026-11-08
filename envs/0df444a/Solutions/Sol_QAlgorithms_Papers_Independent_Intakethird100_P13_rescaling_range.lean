-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P13.rescaling_range
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T18:59:59.96174+00:00
-- url     : https://prove2.me/submissions/ad6d545f-0e21-4f72-a178-c4c5c6658cc5

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P13

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

namespace Aux_P13RR
open QAlgorithms.Papers.Independent.Intakethird100.P13

theorem key (gamma s30 : ℝ) (hg0 : 0 ≤ gamma) (hg1 : gamma ≤ 1)
    (hs0 : 0 ≤ s30) (hs1 : s30 ≤ 1) (hden : 0 < 1-gamma*s30) :
    rescaling gamma s30 ∈ Set.Icc (0 : ℝ) 1 := by
  unfold rescaling
  have hgs : gamma * s30 ≤ gamma := by nlinarith
  refine ⟨div_nonneg (by linarith) hden.le, ?_⟩
  rw [div_le_one hden]
  linarith

end Aux_P13RR

open QAlgorithms.Papers.Independent.Intakethird100.P13 in
theorem solution (gamma s30 : ℝ) (hg0 : 0 ≤ gamma) (hg1 : gamma ≤ 1)
    (hs0 : 0 ≤ s30) (hs1 : s30 ≤ 1) (hden : 0 < 1-gamma*s30) :
    rescaling gamma s30 ∈ Set.Icc (0 : ℝ) 1 := by
  exact Aux_P13RR.key gamma s30 hg0 hg1 hs0 hs1 hden

end
