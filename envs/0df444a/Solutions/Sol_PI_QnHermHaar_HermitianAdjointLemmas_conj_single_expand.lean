-- Prove2me | solution 1 for PI.QnHermHaar.HermitianAdjointLemmas.conj_single_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:37:41.627316+00:00
-- url     : https://prove2.me/submissions/6409f566-8895-4d06-b7d0-cdd428bf72d9

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_Development
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_ElementaryGeneratorAdjoint
import Theorems.Thm_PI_QnHermHaar_HermitianAdjointLemmas_not_out_posL
import Theorems.Thm_PI_QnHermHaar_HermitianAdjointLemmas_hpk_conj_single_apply
import Theorems.Thm_PI_QnHermHaar_HermitianAdjointLemmas_hpk_out_left
import Theorems.Thm_PI_QnHermHaar_HermitianAdjointLemmas_hpk_out_right
import Theorems.Thm_PI_QnHermHaar_HermitianAdjointLemmas_posL_inj
import Theorems.Thm_PI_QnHermHaar_HermitianAdjointLemmas_posL_surj

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
theorem _root_.solution (i : Fin (r + 1)) (a b : Fin (mdim k r i)) :
    Hpk k r * (Matrix.single (posL k r i a) (posL k r i b) (1 : ℂ))ᴴ * Hpk k r =
      ∑ c, ∑ d, (Hm k r i c b * Hm k r i a d) • Matrix.single (posL k r i c) (posL k r i d) (1 : ℂ) := by
  ext p q
  rw [hpk_conj_single_apply]
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero]
  by_cases hp : Out i p
  · rw [hpk_out_left hp (not_out_posL i b), zero_mul]
    symm
    refine Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => if_neg ?_
    rintro ⟨rfl, -⟩
    exact not_out_posL i c hp
  by_cases hq : Out i q
  · rw [hpk_out_right hq (not_out_posL i a), mul_zero]
    symm
    refine Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => if_neg ?_
    rintro ⟨-, rfl⟩
    exact not_out_posL i d hq
  obtain ⟨c₀, rfl⟩ := posL_surj hp
  obtain ⟨d₀, rfl⟩ := posL_surj hq
  rw [Finset.sum_eq_single c₀, Finset.sum_eq_single d₀, if_pos ⟨rfl, rfl⟩]
  · rfl
  · intro d _ hd
    rw [if_neg]
    rintro ⟨-, h⟩
    exact hd (posL_inj h)
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro c _ hc
    refine Finset.sum_eq_zero fun d _ => if_neg ?_
    rintro ⟨h, -⟩
    exact hc (posL_inj h)
  · intro h; exact absurd (Finset.mem_univ _) h
end PI.QnHermHaar.HermitianAdjointLemmas
