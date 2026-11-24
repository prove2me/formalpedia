-- Prove2me | solution 1 for PI.QnHermHaar.HermitianAdjointLemmas.inU_hpart2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:43:56.784902+00:00
-- url     : https://prove2.me/submissions/bb0049a1-c444-4e98-8b99-e3ece12b7355

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_Development
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_ElementaryGeneratorAdjoint
import Theorems.Thm_PI_QnHermHaar_HermitianAdjointLemmas_hpk_inv
import Theorems.Thm_PI_QnHermHaar_HermitianAdjointLemmas_hpk_ct
import Theorems.Thm_PI_QnHermHaar_HermitianAdjointLemmas_hpk_hpk
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_hpk_sq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open PI PI.QnHermHaar
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
open PI.QnHermHaar.HermitianAdjointLemmas
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace PI.QnHermHaar.HermitianAdjointLemmas
theorem _root_.solution (W : Mx k r) :
    (hpart2 (Hpk k r) W)ᴴ * Hpk k r + Hpk k r * hpart2 (Hpk k r) W = 0 := by
  unfold hpart2
  rw [hpk_inv, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hpk_ct, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add]
  simp only [Matrix.mul_assoc, WeylGroupFacts.hpk_sq, hpk_hpk, Matrix.mul_one]
  have hs : star (1 / (2 * Complex.I) : ℂ) = -(1 / (2 * Complex.I)) := by
    rw [star_div₀, star_one, star_mul', Complex.star_def, Complex.conj_I]
    simp [mul_neg, div_neg, map_ofNat]
  rw [hs, neg_smul, neg_add_eq_zero]
  congr 1
  abel
end PI.QnHermHaar.HermitianAdjointLemmas
