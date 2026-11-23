-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.ValUFD.height_span_prime
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:04:31.91114+00:00
-- url     : https://prove2.me/submissions/26e1dcd6-fe14-42fe-8315-df17b17a6a7c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValUFD

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
namespace ReciprocityTheory.ChartRestriction.G.T0.ValUFD
theorem _root_.solution {q : R} (hq : Prime q) : (Ideal.span {q}).height = 1 := by
  have _ : (Ideal.span {q}).IsPrime := (Ideal.span_singleton_prime hq.ne_zero).mpr hq
  apply le_antisymm
  · rw [← Nat.cast_one, Ideal.height_le_iff]
    intro P hPp hlt
    have hPb : P = ⊥ := by
      by_contra hne
      obtain ⟨q', hq'P, hq'⟩ := hPp.exists_mem_prime_of_ne_bot hne
      have hdvd : q ∣ q' := Ideal.mem_span_singleton.mp (hlt.le hq'P)
      have hass := hq.associated_of_dvd hq' hdvd
      have hle : Ideal.span {q} ≤ P :=
        (Ideal.span_singleton_le_iff_mem P).mpr (P.mem_of_dvd hass.symm.dvd hq'P)
      exact absurd hle (not_le_of_gt hlt)
    rw [hPb, Ideal.height_bot]
    exact_mod_cast Nat.zero_lt_one
  · rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot, Ideal.span_singleton_eq_bot]
    exact hq.ne_zero
end ReciprocityTheory.ChartRestriction.G.T0.ValUFD
