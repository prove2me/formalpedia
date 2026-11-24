-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.divByMv_mul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:59:10.151645+00:00
-- url     : https://prove2.me/submissions/33ebe360-9fe2-4a00-b10e-ea177c469be2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralMv_iff_divBy_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_divByMv_mul

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
variable {ι : Type}
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {x : K} {F G : MvPowerSeries ι K} (hF : IntegralMv F) (hG : DivByMv x G) :
    DivByMv x (F * G) := by
  have h := divByMv_mul ((integralMv_iff_divBy_one F).mp hF) hG
  rwa [one_mul] at h
end ReciprocityTheory.ChartRestriction.L1
