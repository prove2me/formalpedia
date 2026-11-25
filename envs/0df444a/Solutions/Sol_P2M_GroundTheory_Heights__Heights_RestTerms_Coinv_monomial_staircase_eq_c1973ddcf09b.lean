-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Coinv_monomial_staircase_eq_c1973ddcf09b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:50:24.076595+00:00
-- url     : https://prove2.me/submissions/22251166-7cce-42cb-a236-5d14b25271f9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsCoinv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCoinvariantTopDegree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace Coinv
theorem _root_.solution (f N : ℕ) :
    (monomial (Coinv.staircase f N) (1 : ℚ) : RootRing f N) =
      ∏ τ : Fin f, ∏ i : Fin N, X (τ, i) ^ (i : ℕ) := by
  rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Fintype.prod_prod_type]
  simp [Coinv.staircase]
end Coinv
end GroundTheory.Heights₂.Heights.RestTerms
