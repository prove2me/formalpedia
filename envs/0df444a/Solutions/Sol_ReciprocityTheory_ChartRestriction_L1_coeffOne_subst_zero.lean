-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.coeffOne_subst_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:19:15.003926+00:00
-- url     : https://prove2.me/submissions/8a22df04-2fe6-4215-8666-1ff108747852

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
theorem _root_.solution {f s : PowerSeries R} (hs : constantCoeff s = 0) :
    coeff 1 (f.subst s) = coeff 1 f * coeff 1 s := by
  have ha : HasSubst s := HasSubst.of_constantCoeff_zero hs
  have hX : X ∣ s := X_dvd_iff.mpr hs
  rw [PowerSeries.coeff_subst' ha, finsum_eq_single _ 1]
  · simp [smul_eq_mul]
  · intro d hd
    rcases Nat.lt_or_gt_of_ne hd with h | h
    · have : d = 0 := by omega
      subst this
      simp
    · have h2 : X ^ d ∣ s ^ d := pow_dvd_pow_of_dvd hX d
      have h3 := X_pow_dvd_iff.mp h2 1 h
      simp [h3]
end ReciprocityTheory.ChartRestriction.L1
