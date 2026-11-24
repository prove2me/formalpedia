-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.FrobField.funEqSetting
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:47:21.915682+00:00
-- url     : https://prove2.me/submissions/969bddfc-5455-45c7-9f7d-70994252e725

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
variable {K : Type} [NormedField K] [IsUltrametricDist K]
variable {l : ℕ} {σ : K →+* K} {ι : Type}
namespace ReciprocityTheory.ChartRestriction.L1
namespace FrobField
theorem _root_.solution [CharZero K] (h : FrobField K l σ) : FunctionalEquationSetting K l l σ := by
  refine ⟨h.prime, ⟨1, one_pos, (pow_one l).symm⟩, h.norm_l, ?_⟩
  exact h.frob
end FrobField
end ReciprocityTheory.ChartRestriction.L1
