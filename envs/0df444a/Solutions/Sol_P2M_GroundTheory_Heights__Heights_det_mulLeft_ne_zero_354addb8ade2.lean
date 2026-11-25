-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_det_mulLeft_ne_zero_354addb8ade2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:29:16.928604+00:00
-- url     : https://prove2.me/submissions/baf50f50-26cc-4481-a945-195392571e09

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PSpecFirstNe

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
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {O B : Type*} [CommRing O] [IsDomain O] [CommRing B] [IsDomain B] [Algebra O B]
    {θ : B} (hθ : θ ≠ 0) : LinearMap.det (LinearMap.mulLeft O θ) ≠ 0 := by
  classical
  intro h
  by_cases H : ∃ s : Finset B, Nonempty (Module.Basis s O B)
  · obtain ⟨s, ⟨b⟩⟩ := H
    have : Module.Free O B := Module.Free.of_basis b
    have hker := LinearMap.bot_lt_ker_of_det_eq_zero h
    rw [bot_lt_iff_ne_bot, Ne, LinearMap.ker_eq_bot] at hker
    exact hker fun x y hxy => mul_left_cancel₀ hθ (by simpa using hxy)
  · simp [LinearMap.coe_det, H] at h
end GroundTheory.Heights₂.Heights
