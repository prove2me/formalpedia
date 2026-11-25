-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Top_constantCoeff_aeval_of_zero_d253147093f5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:54:04.376016+00:00
-- url     : https://prove2.me/submissions/9e85cda1-87d0-419a-ad14-f03f6c03c202

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand

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
theorem _root_.solution {ι κ : Type*} (g : ι → MvPolynomial κ ℚ)
    (hg : ∀ i, constantCoeff (g i) = 0) (p : MvPolynomial ι ℚ) :
    constantCoeff (aeval g p) = constantCoeff p := by
  have : (constantCoeff.comp (aeval g).toRingHom : MvPolynomial ι ℚ →+* ℚ) = constantCoeff := by
    apply MvPolynomial.ringHom_ext
    · intro x; simp [constantCoeff_C]
    · intro i; simp [hg i]
  exact congrArg (fun φ : MvPolynomial ι ℚ →+* ℚ => φ p) this
end GroundTheory.Heights₂.Heights.RestTerms.Top
