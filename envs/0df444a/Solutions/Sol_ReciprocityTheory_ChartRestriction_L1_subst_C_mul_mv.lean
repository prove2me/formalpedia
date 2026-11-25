-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.subst_C_mul_mv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:41:19.74173+00:00
-- url     : https://prove2.me/submissions/3bc3ca07-d9d5-4c07-9891-16bbaad1ae31

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonD

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
variable {R : Type} [CommRing R]
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {ι : Type} {P : MvPowerSeries ι R} (hP : HasSubst P) (c : R)
    (f : PowerSeries R) : (C c * f).subst P = MvPowerSeries.C c * f.subst P := by
  rw [← smul_eq_C_mul, ← MvPowerSeries.smul_eq_C_mul, ← coe_substAlgHom hP, map_smul]
end ReciprocityTheory.ChartRestriction.L1
