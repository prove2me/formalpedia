-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.sum_attach_dite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:35:06.258423+00:00
-- url     : https://prove2.me/submissions/5f9df968-62fa-45ba-bd81-8c997777dafb

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
theorem _root_.solution {X β : Type} [DecidableEq X] [AddCommMonoid β] (S : Finset X) (g : S → β) :
    ∑ x ∈ S.attach, g x = ∑ x ∈ S, (if h : x ∈ S then g ⟨x, h⟩ else 0) := by
  rw [← Finset.sum_attach S (fun x => if h : x ∈ S then g ⟨x, h⟩ else 0)]
  exact Finset.sum_congr rfl fun x _ => by simp only [dif_pos x.2]
end ReciprocityTheory.ChartRestriction.G.DVR
