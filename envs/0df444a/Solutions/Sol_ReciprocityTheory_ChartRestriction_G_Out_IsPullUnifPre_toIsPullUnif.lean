-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.IsPullUnifPre.toIsPullUnif
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:31:46.45282+00:00
-- url     : https://prove2.me/submissions/0300376c-2203-4d97-aafc-1a6a5f47565e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_UnifBaseChangeInjOfSeamsCS

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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out
open Semi
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']
namespace ReciprocityTheory.ChartRestriction.G.Out
namespace IsPullUnifPre
theorem _root_.solution {I : Ideal R} {I' : Ideal R'} {φ : R →+* R'} {D : DegData R I}
    {D' : DegData R' I'} {hD : IsPullDeg φ D.toPre D'.toPre}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {A' : PolAV (Spec (CommRingCat.of (FractionRing R')))}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
    {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G'] [IsCommMonObj G']
    {bc : G' ≅ (Over.pullback (specOf φ)).obj G}
    {U : Unif I D A G} {U' : Unif I' D' A' G'}
    (h : IsPullUnifPre φ hD bc U.toUnifPre U'.toUnifPre) : IsPullUnif φ hD bc U U' :=
  ⟨h⟩
end IsPullUnifPre
end ReciprocityTheory.ChartRestriction.G.Out
