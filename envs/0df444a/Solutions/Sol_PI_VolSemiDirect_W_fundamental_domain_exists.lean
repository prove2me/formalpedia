-- Prove2me | solution 1 for PI.VolSemiDirect.W.fundamental_domain_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:18:48.231266+00:00
-- url     : https://prove2.me/submissions/3fd37aa2-1c83-4bcc-965c-ace6ba363388

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ClosedStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_FundamentalDomainExists
import Theorems.Thm_PI_VolSemiDirect_W_exists_fd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W
open MeasureTheory
namespace PI.VolSemiDirect.W
theorem _root_.solution : FDExG := by
  unfold FDExG
  intro X _ _ _ _ Γ K hK hD
  obtain ⟨hlc, hsc, ht2, htg⟩ := hK
  obtain ⟨hcount, hdisc⟩ := hD
  exact exists_fd (ratG Γ K)
end PI.VolSemiDirect.W
