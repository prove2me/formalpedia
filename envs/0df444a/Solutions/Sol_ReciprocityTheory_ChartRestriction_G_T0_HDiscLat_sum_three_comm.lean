-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.HDiscLat.sum_three_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:50:11.693888+00:00
-- url     : https://prove2.me/submissions/ea035276-cff5-4171-bbdc-04443b29c2df

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open ReciprocityTheory.ChartRestriction.G.T0.HDiscLat
open Module
variable {R F : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field F]
  [Algebra R F] [IsFractionRing R F]
  {ι : Type} [Fintype ι] [DecidableEq ι] {L : ι → Type} [∀ c, Field (L c)] [∀ c, Algebra F (L c)]
  [∀ c, FiniteDimensional F (L c)] [∀ c, Algebra.IsSeparable F (L c)] [∀ c, Algebra R (L c)]
  [∀ c, IsScalarTower R F (L c)]
namespace ReciprocityTheory.ChartRestriction.G.T0.HDiscLat
theorem _root_.solution {α β γ M : Type*} [AddCommMonoid M] (s : Finset α) (t : Finset β) (u : Finset γ)
    (f : α → β → γ → M) :
    ∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ u, f a b c = ∑ c ∈ u, ∑ b ∈ t, ∑ a ∈ s, f a b c := by
  calc ∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ u, f a b c = ∑ a ∈ s, ∑ c ∈ u, ∑ b ∈ t, f a b c :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ c ∈ u, ∑ a ∈ s, ∑ b ∈ t, f a b c := Finset.sum_comm
    _ = ∑ c ∈ u, ∑ b ∈ t, ∑ a ∈ s, f a b c := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
end ReciprocityTheory.ChartRestriction.G.T0.HDiscLat
