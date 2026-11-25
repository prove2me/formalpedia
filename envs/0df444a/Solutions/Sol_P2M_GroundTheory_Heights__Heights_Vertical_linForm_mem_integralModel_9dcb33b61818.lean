-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_linForm_mem_integralModel_9dcb33b61818
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:24:38.472745+00:00
-- url     : https://prove2.me/submissions/2bb2ec7b-fb6c-4aea-8311-f33eddd6674f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PVertSpec

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
variable {K : Type*} [Field K] {n : ℕ}
namespace GroundTheory.Heights₂.Heights.Vertical
theorem _root_.solution {I : Ideal (MvPolynomial (Fin n) K)} {u : Fin n → 𝓞 K}
    (h : linForm u ∈ integralModel I) : linForm (fun j => (u j : K)) ∈ I := by
  simp only [integralModel, Ideal.mem_comap] at h
  convert h using 1
  simp [linForm, map_sum, map_mul, map_C, map_X]
end GroundTheory.Heights₂.Heights.Vertical
