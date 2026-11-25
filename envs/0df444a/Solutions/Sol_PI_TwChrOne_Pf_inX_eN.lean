-- Prove2me | solution 1 for PI.TwChrOne.Pf.inX_eN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:30:20.937539+00:00
-- url     : https://prove2.me/submissions/cb35b2f3-ba47-4129-9bec-aa5ba6f22a86

import Definitions.Def_Formalism_PeriodIntegrals_TwChrOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedCharacterOne_IsIntegralAtSuperdiagonalSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open PI PI.TwChrOne PI.TwChrOne.Pf
variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E))
variable {n : ℕ}
variable {kj N c : ℕ}
namespace PI.TwChrOne.Pf
theorem _root_.solution {j : ℕ} (hj : j < N) : Loc.inX E N c (Loc.eN E N j) = Loc.eN E (N + c) j := by
  funext l
  simp only [Loc.inX, LinearMap.pi_apply]
  by_cases hl : l.1 < N
  · rw [dif_pos hl]
    rfl
  · rw [dif_neg hl, LinearMap.zero_apply]
    unfold Loc.eN
    rw [if_neg (by omega)]
end PI.TwChrOne.Pf
