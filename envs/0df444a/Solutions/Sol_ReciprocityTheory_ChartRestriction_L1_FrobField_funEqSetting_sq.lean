-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.FrobField.funEqSetting_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:06:43.816786+00:00
-- url     : https://prove2.me/submissions/6d1dab65-be90-4d8c-9175-7a0169dc235d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffOneSubstOfConstantCoeffEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_SemilinNormPowSubPow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgFinA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_FrobField_norm_sq_sub_pow_le


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
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ} {σ : K →+* K}
namespace ReciprocityTheory.ChartRestriction.L1
namespace FrobField
theorem _root_.solution [CompleteSpace K] (h : FrobField K l σ) :
    FunctionalEquationSetting K l (l ^ 2) (σ.comp σ) :=
  ⟨h.prime, ⟨2, two_pos, rfl⟩, h.norm_l, fun a ha => h.norm_sq_sub_pow_le a ha⟩
end FrobField
end ReciprocityTheory.ChartRestriction.L1
