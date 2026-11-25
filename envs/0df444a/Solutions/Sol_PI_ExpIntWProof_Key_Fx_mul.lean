-- Prove2me | solution 1 for PI.ExpIntWProof.Key.Fx.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:47:07.132803+00:00
-- url     : https://prove2.me/submissions/20fd26bb-be30-4af3-9104-1b52277d5263

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_RootsOfUnityRingLeWittIntegers
import Theorems.Thm_PI_ExpIntWProof_Key_Fx_common

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
theorem _root_.solution {a b : R} (ha : Fx p a) (hb : Fx p b) : Fx p (a * b) := by
  obtain ⟨f, hf, h1, h2⟩ := Fx.common p ha hb
  exact ⟨f, hf, by rw [mul_pow, h1, h2]⟩
end Fx
end PI.ExpIntWProof.Key
