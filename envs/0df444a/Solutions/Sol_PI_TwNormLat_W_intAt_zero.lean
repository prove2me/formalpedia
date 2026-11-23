-- Prove2me | solution 1 for PI.TwNormLat.W.intAt_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:19:05.669837+00:00
-- url     : https://prove2.me/submissions/53a99944-b53d-41df-96cc-b5bdcf3f7e95

import Definitions.Def_Formalism_PeriodIntegrals_TwNormLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedNormLattice_UniformContinuityGaloisGroup
import Theorems.Thm_P2M_PI_TwNormLat_W_one_notMem__7f2d7b4a1758

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
open PI PI.TwNormLat PI.TwNormLat.W
variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))
namespace PI.TwNormLat.W
theorem _root_.solution : IntAt P (0 : E) := by
  exact ⟨0, 1, PI.TwNormLat.W.one_notMem' P, by simp⟩
end PI.TwNormLat.W
