-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.res_back
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:10:40.629403+00:00
-- url     : https://prove2.me/submissions/02161dec-ee79-4503-aff1-7f096d391cf8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_CartesianLiftThreeCompProjection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBCorr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullGen
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
namespace ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi IsLocalRing
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F]
  {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]
private lemma res_res_lemma {Y : Scheme.{0}} {U W Z : Y.Opens} (h₁ : W ≤ U) (h₂ : Z ≤ W) (x : Γ(Y, U)ˣ) :
    res h₂ (res h₁ x) = res (h₂.trans h₁) x := by
  ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]
  rfl
private lemma res_refl_le {Y : Scheme.{0}} {U : Y.Opens} (h : U ≤ U) (x : Γ(Y, U)ˣ) : res h x = x := by
  ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [show (homOfLE h).op = 𝟙 (Opposite.op U) from Subsingleton.elim _ _]
  simp
section PullFam
variable (hL : D.toPre.P.L.IsLB) (oa : D.toPre.OAct O) (w0 : O)
  (uΨ : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 4)
      ![(padd D.toPre.P.A (𝟙 _) (oa.onB.act w0)).left, 𝟙 D.toPre.P.A.left, (oa.onB.act w0).left,
        (toUnit D.toPre.P.A ≫ η[D.toPre.P.A]).left] ![1, -2, -1, 2]))
  (huΨ : uΨ.IsGen) (a : O) (N : ℕ) (hN : a * star a = (N : O)) (hN1 : 1 ≤ N) (k : ℕ)
end PullFam
end ReciprocityTheory.ChartRestriction.G.DVR
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi IsLocalRing
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F]
  {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution {Y : Scheme.{0}} {U W : Y.Opens} (h₁ : U ≤ W) (h₂ : W ≤ U) (x : Γ(Y, U)ˣ) :
    res h₁ (res h₂ x) = x := by
  rw [res_res_lemma, res_refl_le]
end ReciprocityTheory.ChartRestriction.G.DVR
