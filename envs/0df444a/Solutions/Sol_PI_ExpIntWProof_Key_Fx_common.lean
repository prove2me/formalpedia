-- Prove2me | solution 1 for PI.ExpIntWProof.Key.Fx.common
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:41:34.487841+00:00
-- url     : https://prove2.me/submissions/4d05a177-b7f1-4962-a058-bdc36e9303b6

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_RootsOfUnityRingLeWittIntegers
import Theorems.Thm_PI_ExpIntWProof_Key_pow_pow_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.ExpIntWProof PI.ExpIntWProof.Key
variable {R : Type*} [CommRing R] (p : ℕ) [hp : Fact p.Prime] [CharP R p]
namespace PI.ExpIntWProof.Key
namespace Fx
theorem _root_.solution {a b : R} (ha : Fx p a) (hb : Fx p b) :
    ∃ f : ℕ, 0 < f ∧ a ^ p ^ f = a ∧ b ^ p ^ f = b := by
  obtain ⟨f, hf, hfa⟩ := ha
  obtain ⟨g, hg, hgb⟩ := hb
  refine ⟨f * g, Nat.mul_pos hf hg, pow_pow_mul a p f hfa g, ?_⟩
  rw [mul_comm]; exact pow_pow_mul b p g hgb f
end Fx
end PI.ExpIntWProof.Key
