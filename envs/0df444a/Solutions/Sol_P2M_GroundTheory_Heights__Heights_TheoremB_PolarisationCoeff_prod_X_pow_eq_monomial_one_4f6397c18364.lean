-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TheoremB_PolarisationCoeff_prod_X_pow_eq_monomial_one_4f6397c18364
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:22:28.044856+00:00
-- url     : https://prove2.me/submissions/714ed62d-1202-4bca-a15d-f5ae5a8841cc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MultinomialWeights_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MultinomialWeights_PPolarisationCoeff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.TheoremB
open MvPolynomial Finset
namespace GroundTheory.Heights₂.Heights.TheoremB
namespace PolarisationCoeff
theorem _root_.solution {σ S : Type*} [CommSemiring S] [Fintype σ] (K : σ →₀ ℕ) :
    ∏ v, (X v : MvPolynomial σ S) ^ K v = monomial K 1 := by
  rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
end PolarisationCoeff
end GroundTheory.Heights₂.Heights.TheoremB
