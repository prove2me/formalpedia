-- Prove2me | solution 1 for PI.TwChrOne.Pf.eN_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:30:10.486846+00:00
-- url     : https://prove2.me/submissions/29ac2361-3aa1-40f8-9800-e24bac359383

import Definitions.Def_Formalism_PeriodIntegrals_TwChrOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedCharacterOne_IsIntegralAtSuperdiagonalSum
import Theorems.Thm_PI_TwChrOne_Pf_mem_stdAt_of

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
namespace PI.TwChrOne.Pf
theorem _root_.solution (j : ℕ) : Loc.eN E n j ∈ stdAt E n P := by
  refine mem_stdAt_of P fun i => ?_
  unfold Loc.eN
  split_ifs
  · exact ⟨1, map_one _⟩
  · exact ⟨0, map_zero _⟩
end PI.TwChrOne.Pf
