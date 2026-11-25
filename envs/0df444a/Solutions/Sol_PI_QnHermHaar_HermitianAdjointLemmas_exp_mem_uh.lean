-- Prove2me | solution 1 for PI.QnHermHaar.HermitianAdjointLemmas.exp_mem_uh
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:15:17.034212+00:00
-- url     : https://prove2.me/submissions/b0a7006f-dc6c-4629-9963-375491a65272

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_Development
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_ElementaryGeneratorAdjoint
import Theorems.Thm_PI_QnHermHaar_HermitianAdjointLemmas_hpk_inv
import Theorems.Thm_PI_QnHermHaar_HermitianAdjointLemmas_hpk_isUnit
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
theorem _root_.solution {Y : Mx k r} (hY : Yᴴ * Hpk k r + Hpk k r * Y = 0) :
    NormedSpace.exp Y ∈ UH (Hpk k r) := by
  have h0 : Yᴴ * Hpk k r = -(Hpk k r * Y) := eq_neg_of_add_eq_zero_left hY
  have hYh : Yᴴ = Hpk k r * (-Y) * (Hpk k r)⁻¹ := by
    rw [hpk_inv, Matrix.mul_neg, ← h0, Matrix.mul_assoc, WeylGroupFacts.hpk_sq, Matrix.mul_one]
  have hexp : (NormedSpace.exp Y)ᴴ = Hpk k r * NormedSpace.exp (-Y) * Hpk k r := by
    rw [← Matrix.exp_conjTranspose, hYh, Matrix.exp_conj _ _ hpk_isUnit, hpk_inv]
  have hc : NormedSpace.exp (-Y) * NormedSpace.exp Y = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl Y)), neg_add_cancel,
      NormedSpace.exp_zero]
  show (NormedSpace.exp Y)ᴴ * Hpk k r * NormedSpace.exp Y = Hpk k r
  rw [hexp, Matrix.mul_assoc (Hpk k r * NormedSpace.exp (-Y)) (Hpk k r) (Hpk k r), WeylGroupFacts.hpk_sq,
    Matrix.mul_one, Matrix.mul_assoc, hc, Matrix.mul_one]
end PI.QnHermHaar.HermitianAdjointLemmas
