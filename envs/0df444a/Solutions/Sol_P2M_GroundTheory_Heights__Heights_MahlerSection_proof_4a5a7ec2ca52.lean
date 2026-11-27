-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MahlerSection_proof_4a5a7ec2ca52
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:03:52.751688+00:00
-- url     : https://prove2.me/submissions/06447e99-cb93-44d0-a63f-434be32eb03b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PMahlerSection

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
namespace GroundTheory.Heights₂.Heights
namespace MahlerSection
theorem _root_.solution (h₁ : MahlerSectionOfConst.Statement) (h₂ : DefectConstZero.Statement)
    (h₃ : DefectConstStep.Statement) : MahlerSection.Statement := by
  have hdim : ∀ e, MahlerSectionDim e := by
    intro e
    induction e with
    | zero => exact h₁ 0 h₂
    | succ e ih => exact h₁ (e + 1) (h₃ e ih)
  intro n e δ h Z f u hprime hchow hhom hadm
  exact hdim e n δ h Z f u ⟨hprime, hchow, hhom⟩ hadm
end MahlerSection
end GroundTheory.Heights₂.Heights
