-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.ValUFD.gen_prime
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:39:33.723699+00:00
-- url     : https://prove2.me/submissions/090b93b0-6c62-4fef-91a6-c7f3a815f296

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
variable {gen : Ideal R → R}
namespace ReciprocityTheory.ChartRestriction.G.T0.ValUFD
theorem _root_.solution (hgen : ∀ p : Ideal R, p.IsPrime → p.height = 1 → p = Ideal.span {gen p})
    {p : Ideal R} (hp : p ∈ {p : Ideal R | p.IsPrime ∧ p.height = 1}) : Prime (gen p) := by
  obtain ⟨hpp, hh⟩ := hp
  have hg := hgen p hpp hh
  have hne : gen p ≠ 0 := by
    intro h0
    apply p.ne_bot_of_height_eq_one hh
    rw [hg, h0, Ideal.span_singleton_eq_bot]
  exact (Ideal.span_singleton_prime hne).mp (hg ▸ hpp)
end ReciprocityTheory.ChartRestriction.G.T0.ValUFD
