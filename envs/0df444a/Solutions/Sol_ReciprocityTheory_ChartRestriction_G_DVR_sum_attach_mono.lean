-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.sum_attach_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:27:50.204064+00:00
-- url     : https://prove2.me/submissions/1c12b2ae-09c0-475a-ba0c-1bf2caefa7d2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBCorr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExpIdentRestrict

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))}
  [GrpObj G] [IsCommMonObj G]
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution {X β : Type} [AddCommMonoid β] {S S' : Finset X} (hSS : S ⊆ S')
    (T : S' → β) (h0 : ∀ α : S', α.1 ∉ S → T α = 0) :
    ∑ α ∈ S'.attach, T α = ∑ α ∈ S.attach, T ⟨α.1, hSS α.2⟩ := by
  classical
  set g : X → β := fun α => if h : α ∈ S' then T ⟨α, h⟩ else 0 with hg
  have h1 : ∑ α ∈ S'.attach, T α = ∑ α ∈ S', g α := by
    rw [← Finset.sum_attach S' g]
    exact Finset.sum_congr rfl fun α _ => by simp only [hg, dif_pos α.2]
  have h2 : ∑ α ∈ S.attach, T ⟨α.1, hSS α.2⟩ = ∑ α ∈ S, g α := by
    rw [← Finset.sum_attach S g]
    exact Finset.sum_congr rfl fun α _ => by simp only [hg, dif_pos (hSS α.2)]
  rw [h1, h2]
  exact (Finset.sum_subset hSS fun α hα' hα => by
    simp only [hg, dif_pos hα']
    exact h0 ⟨α, hα'⟩ hα).symm
end ReciprocityTheory.ChartRestriction.G.DVR
