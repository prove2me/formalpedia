-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.ValUFD.gen_dvd_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:04:31.904045+00:00
-- url     : https://prove2.me/submissions/59aa28ae-0b37-4a5c-a7f2-f5de74f22a3d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValUFD
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValUFD_gen_prime

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
    gen p ∣ q ↔ p = Ideal.span {q} := by
  constructor
  · intro h
    rw [hgen p hp.1 hp.2, Ideal.span_singleton_eq_span_singleton]
    exact (gen_prime hgen hp).associated_of_dvd hq h
  · intro h
    subst h
    have h2 := hgen _ hp.1 hp.2
    rw [Ideal.span_singleton_eq_span_singleton] at h2
    exact h2.symm.dvd
end ReciprocityTheory.ChartRestriction.G.T0.ValUFD
