-- Prove2me | solution 1 for PI.TwChrOne.Pf.atN_dI
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:16:41.317925+00:00
-- url     : https://prove2.me/submissions/525a733a-7596-482b-b7a8-2b791213b9e4

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
theorem _root_.solution (v : Sp E (N + c)) (s : Fin (N - kj)) : Loc.atN v (kj + s.1) = v (dI kj N c s) := by
  unfold Loc.atN
  rw [dif_pos (by have := s.2; omega)]
  rfl
end PI.TwChrOne.Pf
