-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_OnW_proof_46b512c3d2e2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:58:24.478067+00:00
-- url     : https://prove2.me/submissions/7e2f67a5-8b2f-4276-a9d9-258e56555641

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepThreeOnWLift
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepThreeOnWGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepThreeOnW

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace StepThree.OnW
theorem _root_.solution (hL : StepThree.OnW.Lift.Statement.{u, w})
    (hG : StepThree.OnW.Gen.Statement.{u, w}) : StepThree.OnW.Statement.{u, w} := by
  intro k _ Ω _ _ N x T hK pp hpp
  obtain ⟨c₁, h₁⟩ := hL k Ω N x T hK pp hpp
  obtain ⟨c₂, h₂⟩ := hG k Ω N x T hK pp hpp
  refine ⟨max c₁ c₂, fun b c hb hc I => ?_⟩
  refine (h₂ b c hb (le_of_max_le_right hc) I).trans (sup_le ?_ le_sup_right)
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨s, hs, hcomp, rfl⟩
  obtain ⟨t, ht, hts⟩ := h₁ b c hb (le_of_max_le_left hc) s hs hcomp
  have he : s I = t - (t - s I) := by abel
  rw [SetLike.mem_coe, he]
  exact Submodule.sub_mem _ (Submodule.mem_sup_left (Submodule.subset_span (SetLike.mem_coe.mpr ht)))
    (Submodule.mem_sup_right (hts I))
end StepThree.OnW
end GroundTheory.Heights₂.Heights.Kleiman
