-- Prove2me | solution 1 for PI.QnHermHaar.restricted_gram_hermitian_involution
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:25:21.660505+00:00
-- url     : https://prove2.me/submissions/b9424c08-3b86-4071-80dc-7ddb951f7f18

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_Development
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_RestrictedGramHermitianInvolution
import Theorems.Thm_PI_QnHermHaar_rel_posL_injective
import Theorems.Thm_PI_QnHermHaar_rel_posL_bound
import Theorems.Thm_PI_QnHermHaar_rel_hpk_off_right
import Theorems.Thm_PI_QnHermHaar_rel_sum_posL
import Theorems.Thm_Formalism_QuantumDeterminants_hpkFacts


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open PI PI.QnHermHaar
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
namespace PI.QnHermHaar
theorem _root_.solution : HmFacts := by
  intro k r i
  obtain ⟨hH, hI, -⟩ := hpkFacts k r
  constructor
  · ext a b
    show star (Hpk k r (posL k r i b) (posL k r i a)) = Hpk k r (posL k r i a) (posL k r i b)
    rw [← Matrix.conjTranspose_apply (Hpk k r), hH]
  · ext a b
    have h1 : (Hm k r i * Hm k r i) a b = (Hpk k r * Hpk k r) (posL k r i a) (posL k r i b) := by
      rw [Matrix.mul_apply, Matrix.mul_apply]
      symm
      refine rel_sum_posL k r i
        (fun q => Hpk k r (posL k r i a) q * Hpk k r q (posL k r i b)) ?_
      intro q hq
      show Hpk k r (posL k r i a) q * Hpk k r q (posL k r i b) = 0
      rw [rel_hpk_off_right k r (posL k r i a) q i.val (rel_posL_bound k r i a) hq, zero_mul]
    rw [h1, hI, Matrix.one_apply, Matrix.one_apply]
    by_cases h : a = b
    · subst h
      simp
    · rw [if_neg h, if_neg (fun e => h (rel_posL_injective k r i e))]
end PI.QnHermHaar
