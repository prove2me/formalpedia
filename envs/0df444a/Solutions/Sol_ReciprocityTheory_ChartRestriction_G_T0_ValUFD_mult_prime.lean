-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.ValUFD.mult_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:29:58.471278+00:00
-- url     : https://prove2.me/submissions/39800408-f4b7-4827-aa3e-2f38e46a9b4e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValUFD
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValUFD_gen_prime
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValUFD_gen_dvd_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open ReciprocityTheory.ChartRestriction.G.T0.ValUFD
variable {R F : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] [Field F]
  [Algebra R F] [IsFractionRing R F]
variable {gen : Ideal R → R}
namespace ReciprocityTheory.ChartRestriction.G.T0.ValUFD
theorem _root_.solution (hgen : ∀ p : Ideal R, p.IsPrime → p.height = 1 → p = Ideal.span {gen p})
    {p : Ideal R} (hp : p ∈ {p : Ideal R | p.IsPrime ∧ p.height = 1}) {q : R} (hq : Prime q) :
    multiplicity (gen p) q = if p = Ideal.span {q} then 1 else 0 := by
  split_ifs with h
  · have hass : Associated (gen p) q :=
      (gen_prime hgen hp).associated_of_dvd hq ((gen_dvd_iff hgen hp hq).mpr h)
    rw [multiplicity_eq_of_associated_left hass.symm, multiplicity_self]
  · exact multiplicity_eq_zero.mpr fun hd => h ((gen_dvd_iff hgen hp hq).mp hd)
end ReciprocityTheory.ChartRestriction.G.T0.ValUFD
