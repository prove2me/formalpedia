-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_chartVar_injective_5f5515fd824a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:24:15.088472+00:00
-- url     : https://prove2.me/submissions/abd02033-849e-4207-82cc-17d37b040eae

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_ComapMaximalIdealParDVR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PNormIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
variable {K : Type*} [Field K] [NumberField K] {n e : ℕ}
namespace GroundTheory.Heights₂.Heights.Vertical
theorem _root_.solution (e n : ℕ) : Function.Injective (chartVar e n) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  induction i using Fin.cases <;> induction i' using Fin.cases <;>
    simp_all [chartVar, Fin.cases_zero, Fin.cases_succ]
end GroundTheory.Heights₂.Heights.Vertical
