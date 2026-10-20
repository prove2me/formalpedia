-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier30.P25.identical_state_testing
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T01:11:31.395214+00:00
-- url     : https://prove2.me/submissions/ff4e38bf-df6e-459d-a858-abcff98fb37a

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P25

noncomputable section

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Frontier30 QAlgorithms.Papers.Independent.Frontier30.P25

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Pinned accepted definitions; assessments record the domains of equivalence.

open QAlgorithms.Papers.Independent.Dependency50.P09 (OneDesign relativeD sandwichedD)

open QAlgorithms.Papers.Independent.Dependency50.P24 (logBits idealCCQ)

open QAlgorithms.Papers.Independent.Information100.P22 (bell)

open QAlgorithms.Papers.Independent.Information100.P58 (testingD)

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity privateState privacyTest)

/-- PDF p.15, (4.2): identical normalized states; epsilon<1 guards log(1-epsilon). -/
theorem solution
    {I : Type*} [Fintype I] [Nonempty I]
    (rho : Matrix I I ℂ) (hrho : IsDensityMatrix rho)
    (eps : ℝ) (heps0 : 0 ≤ eps) (heps1 : eps < 1) :
    testingD eps rho rho = (-logBits (1 - eps) : ℝ) := by
  have hmem : (1 - eps) ∈ {v : ℝ | ∃ T : Matrix I I ℂ, IsEffect T ∧ 1 - eps ≤ effectProb T rho ∧
      v = effectProb T rho} := by
    have hp : effectProb (((1 - eps : ℝ) : ℂ) • (1 : Matrix I I ℂ)) rho = 1 - eps := by
      simp only [effectProb, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, hrho.2,
        smul_eq_mul, mul_one, Complex.ofReal_re]
    refine ⟨((1 - eps : ℝ) : ℂ) • 1, ⟨?_, ?_⟩, hp.ge, hp.symm⟩
    · exact Matrix.PosSemidef.one.smul (Complex.zero_le_real.mpr (by linarith))
    · have : (1 : Matrix I I ℂ) - ((1 - eps : ℝ) : ℂ) • 1 = ((eps : ℝ) : ℂ) • 1 := by
        rw [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]; abel
      rw [this]
      exact Matrix.PosSemidef.one.smul (Complex.zero_le_real.mpr heps0)
  have hβ : Information100.P58.testingBeta eps rho rho = 1 - eps := by
    apply le_antisymm
    · exact csInf_le ⟨1 - eps, by rintro v ⟨T, -, h, rfl⟩; exact h⟩ hmem
    · exact le_csInf ⟨_, hmem⟩ (by rintro v ⟨T, -, h, rfl⟩; exact h)
  unfold testingD
  rw [hβ, if_neg (by linarith)]
  rfl


end

