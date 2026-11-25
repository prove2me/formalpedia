-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_proof_16e6dc336e3c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:20:17.001228+00:00
-- url     : https://prove2.me/submissions/87534db6-fba3-4d9b-b0da-bee46c7378be

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepTwo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrictTwist
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_restrictData_twistSys_38c0f50bf705
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_restrictData_twist_6e1cc4ecee74

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
open GroundTheory.Heights₂.Heights.Kleiman.RestrictTwist
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {K' : Type w} [Field K'] [Algebra S K']
variable {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'} {hxy : ∀ i, y i ≠ 0 → x i ≠ 0}
namespace GroundTheory.Heights₂.Heights.Kleiman.RestrictTwist
theorem _root_.solution : Statement.{u, w} := by
  refine ⟨?_, ?_⟩
  · intro S _ Ω _ _ N x K' _ _ y hxy hle c
    exact ⟨_, restrictData_twistSys hxy hle c⟩
  · intro S _ Ω _ _ N x K' _ _ y hxy Q₁ Q₂ Q₁' Q₂' r₁ r₂ h₁ h₂
    exact restrictData_twist h₁ h₂
end GroundTheory.Heights₂.Heights.Kleiman.RestrictTwist
