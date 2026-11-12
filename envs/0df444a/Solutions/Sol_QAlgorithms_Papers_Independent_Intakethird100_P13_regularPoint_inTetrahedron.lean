-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P13.regularPoint_inTetrahedron
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-11T23:46:53.236258+00:00
-- url     : https://prove2.me/submissions/f04b50eb-90ec-4798-8924-119f886da92a

import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P13_rescaling_range
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P13_contraction_preservesTetrahedron
import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P13
open QAlgorithms.Papers.Independent.Intakethird100.P13


noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder



attribute [local instance] Classical.propDecidable Classical.decEq

/-- arXiv:1706.05384v2 PDF pp.12--13, Corollary 23, Eq.(C3), positive S30 case.
The constructed point uses the regular quotient domain of Lemma 20. -/
theorem solution (gamma s30 : ℝ) (hg0 : 0 ≤ gamma) (hg1 : gamma ≤ 1)
    (hs0 : 0 ≤ s30) (hs1 : s30 ≤ 1) (hden : 0 < 1-gamma*s30)
    (s : BlochCoordinates) (hs : s ∈ pauliTetrahedron) :
    regularPauliPoint gamma s30 s ∈ pauliTetrahedron := by
  have hr := rescaling_range gamma s30 hg0 hg1 hs0 hs1 hden
  exact contraction_preservesTetrahedron (rescaling gamma s30) hr.1 hr.2 s hs
