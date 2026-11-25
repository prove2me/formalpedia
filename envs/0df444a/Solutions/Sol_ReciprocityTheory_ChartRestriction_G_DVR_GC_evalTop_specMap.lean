-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.GC.evalTop_specMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:46:48.877881+00:00
-- url     : https://prove2.me/submissions/962cfa76-05a6-4e00-925a-14aec544d175

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_QuadTie
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_GenCalc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
namespace ReciprocityTheory.ChartRestriction.G.DVR.GC
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi IsLocalRing
section Points
variable {V : Type} [CommRing V] [IsDomain V] (F : Type) [Field F] [Algebra (FractionRing V) F]
end Points
section Sep
variable {V : Type} [CommRing V] [IsDomain V] (F : Type) [Field F] [Algebra (FractionRing V) F]
  (P : PolAV (Spec (CommRingCat.of V)))
end Sep
section Fam
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
  [Algebra (FractionRing R) F]
end Fam
section Eval
private theorem presheaf_map_endo_apply (X : Scheme.{0}) {U : X.Opens} (i : U ⟶ U) (a : Γ(X, U)) :
    (X.presheaf.map i.op).hom a = a := by
  rw [show i = 𝟙 U from rfl, op_id, CategoryTheory.Functor.map_id]; rfl
variable {V : Type} [CommRing V] [IsDomain V] (F : Type) [Field F] [Algebra (FractionRing V) F]
end Eval
section EvalMore
end EvalMore
section Val
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)}
end Val
section PullGen
end PullGen
section ValMain
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {v : AddValuation F (WithTop ℚ)}
end ValMain
end ReciprocityTheory.ChartRestriction.G.DVR.GC
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.GC
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi IsLocalRing
namespace ReciprocityTheory.ChartRestriction.G.DVR.GC
theorem _root_.solution {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (U : (Spec (CommRingCat.of A)).Opens) (hU : U = ⊤)
    (hU' : Spec.map (CommRingCat.ofHom f) ⁻¹ᵁ U = ⊤) (a : Γ(Spec (CommRingCat.of A), U)) :
    evalTop _ hU' (((Spec.map (CommRingCat.ofHom f)).app U).hom a) = f (evalTop U hU a) := by
  subst hU
  simp only [evalTop, RingHom.comp_apply]
  rw [show (homOfLE hU'.ge).op = 𝟙 _ from rfl]
  erw [CategoryTheory.Functor.map_id]
  rw [presheaf_map_endo_apply]
  exact congrArg (fun φ => φ.hom a) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f))
end ReciprocityTheory.ChartRestriction.G.DVR.GC
