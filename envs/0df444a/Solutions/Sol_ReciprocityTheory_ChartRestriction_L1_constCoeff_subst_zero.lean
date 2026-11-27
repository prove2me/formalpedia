-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.constCoeff_subst_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:27:42.681704+00:00
-- url     : https://prove2.me/submissions/625c61c5-6bcd-477d-a737-5bfbd238b076

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
theorem _root_.solution {g s : PowerSeries R} (hs : constantCoeff s = 0) :
    constantCoeff (g.subst s) = constantCoeff g := by
  have ha : HasSubst s := HasSubst.of_constantCoeff_zero hs
  rw [← coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_subst' ha, finsum_eq_single _ 0]
  · simp
  · intro d hd
    simp [map_pow, hs, zero_pow hd]
end ReciprocityTheory.ChartRestriction.L1
