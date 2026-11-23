-- Prove2me | solution 1 for P2M_GlobalTheory_Capelli_pderiv_X_mul__2a5262d9a5e3
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:50:36.2538+00:00
-- url     : https://prove2.me/submissions/8b47181b-03ab-4924-a8e9-48fd5f09d58d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CommuteRowOpRightMixedOp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.Capelli
variable {K σ : Type*} [CommRing K]
namespace GlobalTheory.Capelli
theorem _root_.solution [DecidableEq σ] (v w : σ) (Q : MvPolynomial σ K) :
    pderiv v (X w * Q) = X w * pderiv v Q + (if v = w then Q else 0) := by
  simp only [Derivation.leibniz, smul_eq_mul, pderiv_X, Pi.single_apply]
  by_cases h : v = w
  · simp [h]
  · simp [h, Ne.symm h]
end GlobalTheory.Capelli
