-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.TG.expandsAt_scale
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:21:07.754504+00:00
-- url     : https://prove2.me/submissions/2bd58ada-56b7-43cc-8e39-5b98725da25d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGenLevel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGenDiv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_TG_app_toW
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_TG_pG_struct
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_TG_toW_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_TG_toW_res


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
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.TG
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
namespace ReciprocityTheory.ChartRestriction.G.DVR.TG
theorem _root_.solution (U : UnifPre I D A G) (c : R) (τ τ' : H0 U.LG.L 1)
    (hτ : ∀ j, τ'.f j = toW G.hom _ c * τ.f j)
    (g g' : ∀ α, D.toPre.SecB 1 α) (hg : ∀ α j, (g' α).f j = toW D.toPre.P.A.hom _ c * (g α).f j)
    (e : ℕ) (h : U.ExpandsAt e 1 τ g) : U.ExpandsAt e 1 τ' g' := by
  obtain ⟨S, hout, hmain⟩ := h
  refine ⟨S, fun α hα j => ?_, fun p j₁ jf jt hj hcoh => ?_⟩
  · erw [hg α j, map_mul, hout α hα j, mul_zero]
  · have E : expL U e p j₁ S jf jt τ = expR U e p j₁ S jf jt g := hmain p j₁ jf jt hj hcoh
    show expL U e p j₁ S jf jt τ' = expR U e p j₁ S jf jt g'
    set c1 := toW (X := (thickObj R I e G).left) ((fstG I e G).left ≫ G.hom) (U.expW e p j₁ S jf jt) c
    have hL : expL U e p j₁ S jf jt τ' = c1 * expL U e p j₁ S jf jt τ := by
      simp only [expL]
      erw [hτ j₁, map_mul, map_mul, app_toW, toW_res]
      ring
    have hR : expR U e p j₁ S jf jt g' = c1 * expR U e p j₁ S jf jt g := by
      simp only [expR, Finset.mul_sum]
      refine Finset.sum_congr rfl fun α _ => ?_
      erw [hg α.1 (jf α.1), map_mul, map_mul, app_toW, toW_res, toW_congr (pG_struct _)]
      ring
    rw [hL, hR, E]
end ReciprocityTheory.ChartRestriction.G.DVR.TG
