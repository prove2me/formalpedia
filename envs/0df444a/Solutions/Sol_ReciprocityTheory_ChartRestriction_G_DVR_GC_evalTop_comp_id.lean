-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.GC.evalTop_comp_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:46:43.17281+00:00
-- url     : https://prove2.me/submissions/e02a8c95-b926-4960-9e6f-0048f7daf6ee

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
theorem _root_.solution {A : Type} [CommRing A] {Y : Scheme.{0}} (g₁ : Spec (CommRingCat.of A) ⟶ Y)
    (g₂ : Y ⟶ Spec (CommRingCat.of A)) (h : g₁ ≫ g₂ = 𝟙 _) (hU : g₁ ⁻¹ᵁ (g₂ ⁻¹ᵁ ⊤) = ⊤)
    (y : Γ(Spec (CommRingCat.of A), ⊤)) :
    evalTop _ hU ((g₁.app _).hom ((g₂.app ⊤).hom y)) = evalTop ⊤ rfl y := by
  simp only [evalTop, RingHom.comp_apply]
  rw [show (g₁.app (g₂ ⁻¹ᵁ ⊤)).hom ((g₂.app ⊤).hom y) = ((g₁ ≫ g₂).app ⊤).hom y from rfl,
    Scheme.Hom.congr_app h, CommRingCat.hom_comp, RingHom.comp_apply, Scheme.Hom.id_app]
  erw [res_res_lemma _ _ _ (homOfLE (le_refl (⊤ : (Spec (CommRingCat.of A)).Opens)))]
end ReciprocityTheory.ChartRestriction.G.DVR.GC
