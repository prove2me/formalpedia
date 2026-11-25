-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.subst_C_mul_ps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:39:46.74264+00:00
-- url     : https://prove2.me/submissions/29c6cdf4-0ccd-4ee5-9778-35432d4201d8

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
theorem _root_.solution {P : PowerSeries R} (hP : HasSubst P) (c : R)
    (f : PowerSeries R) : (C c * f).subst P = C c * f.subst P := by
  rw [← smul_eq_C_mul, ← smul_eq_C_mul, ← coe_substAlgHom hP, map_smul]
end ReciprocityTheory.ChartRestriction.L1
