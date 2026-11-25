-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_isRadicalAt_of_isRadical_90f13697c733
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:33:16.837323+00:00
-- url     : https://prove2.me/submissions/261f3334-30df-4480-b40f-4b9ecae29e62

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceObjects

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
open MvPolynomial Matrix ComplexSets
noncomputable section
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {I : Ideal (MvPolynomial (Fin n) ℂ)} (hI : I.IsRadical)
    (q : Fin n → ℂ) : IsRadicalAt I q :=
  fun f hf => ⟨1, by simp, by rw [one_mul]; exact hI hf⟩
end GroundTheory.Heights₂.Heights
