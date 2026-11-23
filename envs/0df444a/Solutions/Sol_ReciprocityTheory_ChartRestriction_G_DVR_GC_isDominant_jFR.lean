-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.GC.isDominant_jFR
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:14:43.570798+00:00
-- url     : https://prove2.me/submissions/266d1c84-21ef-43bd-af61-73f77fce483d

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
namespace ReciprocityTheory.ChartRestriction.G.DVR.GC
theorem _root_.solution : IsDominant (DegPre.jFR (R := V) F) := by
  rw [jFR_eq']
  refine ⟨?_⟩
  rw [Spec.map_base]
  have hinj : Function.Injective ((algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V))) :=
    (algebraMap (FractionRing V) F).injective.comp (IsFractionRing.injective V (FractionRing V))
  refine (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (fun x hx => ?_)
  have hx' : ((algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V))) x = 0 := hx
  rw [show x = 0 from hinj (hx'.trans (map_zero _).symm)]
  exact zero_mem _
end ReciprocityTheory.ChartRestriction.G.DVR.GC
