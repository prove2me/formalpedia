-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_parIdx_injective_fcb9d9eec217
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:23:27.619859+00:00
-- url     : https://prove2.me/submissions/249c9d1b-ec21-4190-9ea0-a77c9a8d2bbb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecBFinite

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
open GroundTheory.Heights₂.Heights.Vertical.SecBFinite
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Heights₂.Heights.Vertical.SecBFinite
theorem _root_.solution (e n : ℕ) : Function.Injective (parIdx e n) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  induction i using Fin.cases <;> induction i' using Fin.cases <;> simp_all [parIdx]
end GroundTheory.Heights₂.Heights.Vertical.SecBFinite
