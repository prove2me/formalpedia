-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.honF_integral_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:37:18.01292+00:00
-- url     : https://prove2.me/submissions/38db938a-4af0-445a-980b-4c0538920840

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_SubstOfLog
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonF
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralMv_subst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralPS_iff_mv


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
variable {lam : PowerSeries K} {Φ : MvPowerSeries (Fin 2) K} {A : PowerSeries K} {a : K}
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {f g : PowerSeries K} (hf : IntegralPS f) (hg0 : constantCoeff g = 0)
    (hg : IntegralPS g) : IntegralPS (f.subst g) :=
  (integralPS_iff_mv _).mpr (integralMv_subst hf hg0 ((integralPS_iff_mv g).mp hg))
end ReciprocityTheory.ChartRestriction.L1
