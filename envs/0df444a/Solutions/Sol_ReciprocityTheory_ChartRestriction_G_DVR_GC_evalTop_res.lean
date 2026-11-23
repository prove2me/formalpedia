-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.GC.evalTop_res
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:15:02.3535+00:00
-- url     : https://prove2.me/submissions/92d02f22-4b93-4269-9bf2-1fd2534fe568

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
private theorem res_res_lemma (X : Scheme.{0}) {U V W : X.Opens} (i : V ⟶ U) (j : W ⟶ V) (k : W ⟶ U)
    (a : Γ(X, U)) : (X.presheaf.map j.op).hom ((X.presheaf.map i.op).hom a) = (X.presheaf.map k.op).hom a := by
  have : X.presheaf.map i.op ≫ X.presheaf.map j.op = X.presheaf.map k.op := by
    rw [← Functor.map_comp]; rfl
  rw [← this]; rfl
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
theorem _root_.solution {A : Type} [CommRing A] {U U' : (Spec (CommRingCat.of A)).Opens} (h : U' ≤ U)
    (hU : U = ⊤) (hU' : U' = ⊤) (a : Γ(Spec (CommRingCat.of A), U)) :
    evalTop U' hU' (((Spec (CommRingCat.of A)).presheaf.map (homOfLE h).op).hom a) = evalTop U hU a := by
  simp only [evalTop, RingHom.comp_apply]
  rw [res_res_lemma _ _ _ (homOfLE hU.ge)]
end ReciprocityTheory.ChartRestriction.G.DVR.GC
