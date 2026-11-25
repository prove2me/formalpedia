-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.shape_secRel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:12:29.451652+00:00
-- url     : https://prove2.me/submissions/12a3947a-704f-49f8-9e07-d4dd9bddaa4f

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
section PullFam
variable (hL : D.toPre.P.L.IsLB) (oa : D.toPre.OAct O) (w0 : O)
  (uΨ : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 4)
      ![(padd D.toPre.P.A (𝟙 _) (oa.onB.act w0)).left, 𝟙 D.toPre.P.A.left, (oa.onB.act w0).left,
        (toUnit D.toPre.P.A ≫ η[D.toPre.P.A]).left] ![1, -2, -1, 2]))
  (huΨ : uΨ.IsGen) (a : O) (N : ℕ) (hN : a * star a = (N : O)) (hN1 : 1 ≤ N) (k : ℕ)
end PullFam
private lemma rs_rs_eq_rs_trans {Y : Scheme.{0}} {U W Z : Y.Opens} (h₁ : W ≤ U) (h₂ : Z ≤ W) (x : Γ(Y, U)) :
    rs h₂ (rs h₁ x) = rs (h₂.trans h₁) x := by
  simp only [rs]
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]
  rfl
private lemma rs_mul' {Y : Scheme.{0}} {U W : Y.Opens} (h : W ≤ U) (x y : Γ(Y, U)) :
    rs h (x * y) = rs h x * rs h y := map_mul _ _ _
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
theorem _root_.solution {Y : Scheme.{0}} {U₁ U₂ U₃ W V₂ O : Y.Opens} (hW : W ≤ U₃) (hWV : W ≤ V₂) (hV : V₂ ≤ U₂)
    (o : O ≤ W ⊓ U₁) (o₁ : O ≤ U₁) (o₂ : O ≤ U₂) (o₃ : O ≤ U₃) (x : Γ(Y, U₁)) (y : Γ(Y, U₂)) (u : Γ(Y, U₃)ˣ)
    (e : rs (inf_le_left : W ⊓ U₁ ≤ W) (rs hW (u : Γ(Y, U₃)) * rs hWV (rs hV y)) =
      rs (inf_le_right : W ⊓ U₁ ≤ U₁) x) :
    rs o₁ x = rs o₂ y * rs o₃ (u : Γ(Y, U₃)) := by
  have e2 := congrArg (fun z => rs o z) e
  simp only [rs_rs_eq_rs_trans, rs_mul'] at e2
  rw [mul_comm]
  exact e2.symm
end ReciprocityTheory.ChartRestriction.G.DVR
