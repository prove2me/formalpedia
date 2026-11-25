-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_StepThreeOnWLift_piece_le_idealGraded_85f2dd901128
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:15:39.479988+00:00
-- url     : https://prove2.me/submissions/108a8e09-1924-4afe-b699-266406d7c62e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepThreeOnWLift
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsClaimSeq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PClaimVanish
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSurjectiveClosed
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepThreeOnWLift

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
open GroundTheory.Heights₂.Heights.Kleiman.StepThreeOnWLift
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.StepThreeOnWLift
theorem _root_.solution {J P : Ideal (Poly k N)} (hJP : J ≤ P) (Jg : FinGradedSub (S := k) (x := x) Ω)
    (hJg : ∀ c : ℤ, Jg.piece c = Submodule.span k {z | ∃ (f : Poly k N) (e : ℕ), f ∈ J ∧
      f.IsHomogeneous e ∧ (e : ℤ) = c ∧ z = aeval x f}) :
    ∀ c, Jg.piece c ≤ (idealGraded x P).piece c := by
  intro c
  rw [hJg]
  refine Submodule.span_mono ?_
  rintro _ ⟨f, e, hf, hfe, he, rfl⟩
  exact ⟨f, e, hJP hf, hfe, he, rfl⟩
end GroundTheory.Heights₂.Heights.Kleiman.StepThreeOnWLift
