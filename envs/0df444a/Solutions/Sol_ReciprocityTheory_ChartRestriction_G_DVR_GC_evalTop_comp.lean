-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.GC.evalTop_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:00:41.094632+00:00
-- url     : https://prove2.me/submissions/259c1d68-b893-4134-ab0d-a9f159b05b69

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_QuadTie
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_GenCalc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_GC_evalTop_of_eq
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
private theorem jFR_eq' : DegPre.jFR (R := V) F = Spec.map (CommRingCat.ofHom
    ((algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V)))) := by
  simp only [DegPre.jFR, jFK, jK, ← Spec.map_comp]
  rfl
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
variable {V : Type} [CommRing V] [IsDomain V] (F : Type) [Field F] [Algebra (FractionRing V) F]
set_option maxHeartbeats 800000
namespace ReciprocityTheory.ChartRestriction.G.DVR.GC
theorem _root_.solution {Y : Scheme.{0}} (g : Spec (CommRingCat.of F) ⟶ Y) (e : Spec (CommRingCat.of V) ⟶ Y)
    (hg : g = DegPre.jFR (R := V) F ≫ e) (U : Y.Opens) (hU : e ⁻¹ᵁ U = ⊤) (hU' : g ⁻¹ᵁ U = ⊤)
    (a : Γ(Y, U)) :
    evalTop _ hU' ((g.app U).hom a) =
      algebraMap (FractionRing V) F (algebraMap V (FractionRing V) (evalTop _ hU ((e.app U).hom a))) := by
  subst hg
  have h1 := evalTop_of_eq ((algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V)))
    (DegPre.jFR (R := V) F) (jFR_eq' F) (e ⁻¹ᵁ U) hU hU' ((e.app U).hom a)
  exact h1
end ReciprocityTheory.ChartRestriction.G.DVR.GC
