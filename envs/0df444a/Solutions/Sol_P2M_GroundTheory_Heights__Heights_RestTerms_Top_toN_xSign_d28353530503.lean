-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Top_toN_xSign_d28353530503
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:12:23.291162+00:00
-- url     : https://prove2.me/submissions/619febd1-8003-414b-9d1f-cd9bb1813f44

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_BlockValue

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.RestTerms
open GroundTheory.Heights₂.Heights.RestTerms.Top
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms.Top
theorem _root_.solution (r a : ℕ) (c : SmallBlock) (p : MvPolynomial (Fin (r + a)) ℚ) :
    toN (r + a) (xSign r a c p) = aeval (fun i : Fin (r + a) => C c.sign * X i) p := by
  have key : (toN (r + a)).comp (xSign r a c) =
      aeval (fun i : Fin (r + a) => C c.sign * X i) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [toN, xSign]
  exact congrArg (fun φ : MvPolynomial (Fin (r + a)) ℚ →ₐ[ℚ] MvPolynomial (Fin (r + a)) ℚ => φ p) key
end GroundTheory.Heights₂.Heights.RestTerms.Top
