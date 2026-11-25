-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_claim_le_346deb24d81f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:21:43.230795+00:00
-- url     : https://prove2.me/submissions/8c8835f0-b6d8-4c0c-9b0d-de1280ea614c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsClaimSeq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PClaimVanishCech
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PClaimVanish

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
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
variable (T : StepData k x) (Jg : FinGradedSub (S := k) (x := x) Ω)
  (hJg : ∀ c : ℤ, Jg.piece c = Submodule.span k {z | ∃ (f : Poly k N) (e : ℕ), f ∈ T.J ∧
    f.IsHomogeneous e ∧ (e : ℤ) = c ∧ z = aeval x f})
include hJg
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution : ∀ c, Jg.piece c ≤ (coordGraded k x).piece c := by
  intro c
  rw [hJg]
  refine Submodule.span_mono ?_
  rintro _ ⟨f, e, -, hf, he, rfl⟩
  exact ⟨f, e, hf, he, rfl⟩
end GroundTheory.Heights₂.Heights.Kleiman
