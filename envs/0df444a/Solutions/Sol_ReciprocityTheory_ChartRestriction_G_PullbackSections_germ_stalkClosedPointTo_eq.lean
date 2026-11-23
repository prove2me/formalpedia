-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.germ_stalkClosedPointTo_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:29:14.200263+00:00
-- url     : https://prove2.me/submissions/17000fbb-feab-4def-a0d2-5a0791cd54d4

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SubConstMemOrig
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetA

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
variable {Y : Scheme.{0}}
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution {R : CommRingCat.{0}} [IsLocalRing R] (f : Spec R ⟶ Y) (U : Y.Opens)
    (hU : f (IsLocalRing.closedPoint R) ∈ U) :
    Y.presheaf.germ U _ hU ≫ Scheme.stalkClosedPointTo f =
      f.appLE U ⊤ (Scheme.preimage_eq_top_of_closedPoint_mem f hU).ge ≫ (Scheme.ΓSpecIso R).hom := by
  rw [Scheme.germ_stalkClosedPointTo, Scheme.Hom.appLE]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom, Category.assoc]
  first
  | rfl
  | congr 3
end ReciprocityTheory.ChartRestriction.G.PullbackSections
