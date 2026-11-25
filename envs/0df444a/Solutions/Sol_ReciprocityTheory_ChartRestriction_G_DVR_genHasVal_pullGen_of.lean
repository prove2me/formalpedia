-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.genHasVal_pullGen_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:27:10.46725+00:00
-- url     : https://prove2.me/submissions/63c3af8d-ba14-40c1-a460-7d19d264d47c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_WchartLePreimage
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullU_comp


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
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution {X Y : Scheme.{0}} (L : LB X) {Ix : Type} [Fintype Ix] (φ : Ix → (Y ⟶ X))
    (ε : Ix → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (p : Spec (CommRingCat.of V) ⟶ Y)
    (q : Spec (CommRingCat.of (FractionRing V)) ⟶ Y) (hq : q = jK V ≫ p) :
    GenHasVal ϖ L (fun k => p ≫ φ k) (fun k => q ≫ φ k) (fun k => by rw [hq, Category.assoc]) ε
      (LB.pullGen L φ ε t q) 0 := by
  subst hq
  have gen2 : ∀ {A B : Scheme.{0}} (f : A ⟶ B) (U U' : B.Opens) (hU : U' ≤ U) (W : A.Opens)
      (hW : W ≤ f ⁻¹ᵁ U') (x : Γ(B, U)ˣ),
      res hW (pullU f U' (res hU x)) = res (fun y hy => hU (hW hy) : W ≤ f ⁻¹ᵁ U) (pullU f U x) := by
    intro A B f U U' hU W hW x
    apply Units.ext
    have hm : (B.presheaf.map (homOfLE hU).op ≫ f.app U') ≫ A.presheaf.map (homOfLE hW).op =
        f.app U ≫ A.presheaf.map (homOfLE (fun y hy => hU (hW hy) : W ≤ f ⁻¹ᵁ U)).op := by
      rw [Scheme.Hom.naturality, Category.assoc, ← Functor.map_comp]
      rfl
    exact congrArg (fun m => m.hom x.val) hm
  have gen4 : ∀ {A B C : Scheme.{0}} (f : A ⟶ B) (g : B ⟶ C) (U : C.Opens) (U' : B.Opens)
      (hU' : U' ≤ g ⁻¹ᵁ U) (W : A.Opens) (h1 : W ≤ (f ≫ g) ⁻¹ᵁ U) (h2 : W ≤ f ⁻¹ᵁ U')
      (x : Γ(C, U)ˣ), res h1 (pullU (f ≫ g) U x) = res h2 (pullU f U' (res hU' (pullU g U x))) := by
    intro A B C f g U U' hU' W h1 h2 x
    rw [pullU_comp, gen2]
    rfl
  refine ⟨LB.pullGen L φ ε t p, pullGen_isGen L φ ε t ht p, 1, ⟨1, by simp⟩, fun j => ?_⟩
  simp only [scal, resTop, map_one]
  refine Eq.trans ?_ (one_mul _).symm
  exact congrArg Units.val (gen4 (jK V) p (LB.wchart L φ j) (LB.wchart L (fun k => p ≫ φ k) j) _ _ _ _ (t.s j))
end ReciprocityTheory.ChartRestriction.G.DVR
