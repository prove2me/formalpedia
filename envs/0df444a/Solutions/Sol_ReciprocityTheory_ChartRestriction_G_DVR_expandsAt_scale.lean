-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.expandsAt_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:44:59.816107+00:00
-- url     : https://prove2.me/submissions/2f1a2d45-7b55-402f-b9d3-74b55f0a56b8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_RValue
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExpandsAtScale
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_const_pull__01ca0e928de5

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution (U : UnifPre I D A G) (e k : ℕ)
    (σ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))))
    (f : ∀ α : D.toPre.X, D.toPre.SecB k α) (r : R) (h : U.ExpandsAt e k σ f) :
    U.ExpandsAt e k (SecOps.secScale (scal G.hom r) σ)
      (fun α => SecOps.secScale (scal D.toPre.P.A.hom r) (f α)) := by
  obtain ⟨S, hvan, hid⟩ := h
  refine ⟨S, fun α hα j => ?_, fun p j₁ jf jt h1 hcoh => ?_⟩
  · show ((U.gt e).pG.left.app _).hom (resTop _ (scal D.toPre.P.A.hom r) * (f α).f j) = 0
    rw [map_mul, hvan α hα j, mul_zero]
  · have e0 := hid p j₁ jf jt h1 hcoh
    set W := U.expW e p j₁ S jf jt
    have hG : (fstG I e G).left ≫ G.hom = ((Over.map (thick R I e)).obj (thickObj R I e G)).hom := Over.w _
    have hB : (U.gt e).pG.left ≫ D.toPre.P.A.hom = ((Over.map (thick R I e)).obj (thickObj R I e G)).hom :=
      Over.w _
    have e1 := congrArg (fun x => resTop W (scal ((Over.map (thick R I e)).obj (thickObj R I e G)).hom r) * x) e0
    simp only [Finset.mul_sum] at e1
    convert e1 using 1
    · simp only [SecOps.secScale]
      erw [map_mul, map_mul, const_pull' (fstG I e G).left _ G.hom (Over.w _) r (U := U.LG.L.wchart (fun _ => 𝟙 G.left) j₁)]
      exact mul_left_comm _ _ _
    · refine Finset.sum_congr rfl (fun α _ => ?_)
      simp only [SecOps.secScale]
      erw [map_mul, map_mul, const_pull' (U.gt e).pG.left _ D.toPre.P.A.hom (Over.w _) r (U := D.toPre.P.L.wchart (D.toPre.famφB α.1) (jf α.1))]
      exact mul_assoc _ _ _
end ReciprocityTheory.ChartRestriction.G.DVR
