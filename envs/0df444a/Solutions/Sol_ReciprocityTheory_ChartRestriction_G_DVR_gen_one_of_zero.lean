-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.gen_one_of_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:37:48.959265+00:00
-- url     : https://prove2.me/submissions/4eef671f-9d2e-4172-981a-e75f993c2b2f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_RValue
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExpandsAtScale
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_b_units_const
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_res_refl__cb32e03a41c1
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_res_res__b0a8af1c3378
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_corr_pullGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_corr_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_corr_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_eq_one_of_res_top
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_fsum_empty
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_gen_transport
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pull_pull_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_res_back
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_sameSum_iff_fsum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_units_map_eq_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_wchart_empty


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
open scoped Classical
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution (hGF : GlobalFnsSt) (D : DegData V (maximalIdeal V)) {K : Type} [Fintype K]
    (φ : K → (D.toPre.P.A.left ⟶ D.toPre.P.A.left)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb D.toPre.P.L φ ε)) (ht : t.IsGen) (h0 : fsum φ ε = 0)
    (hv : LB.Gen.Corr D.toPre.P.L _ _ (K' := PEmpty) PEmpty.elim PEmpty.elim
      (LB.pullGen D.toPre.P.L φ ε t (eSec D.toPre.P.A)) (LB.oneGen D.toPre.P.L)) :
    ∀ j, LB.Coh D.toPre.P.L φ j → t.s j = 1 := by
  have hL : D.toPre.P.L.IsLB := D.toPre.P.isLB
  have hs0 : LB.SameSum φ ε (K' := PEmpty) PEmpty.elim PEmpty.elim := by
    rw [sameSum_iff_fsum, h0, fsum_empty]
  obtain ⟨te, -, c2⟩ := gen_transport hL hs0 t ht
  let j0 : PEmpty → D.toPre.P.L.ι := PEmpty.elim
  let f : Γ(D.toPre.P.A.left, ⊤)ˣ := res (le_of_eq (wchart_empty j0).symm) (te.s j0)
  obtain ⟨c, hc⟩ := b_units_const hGF D f
  have hte : te.s j0 = res (fun _ _ => trivial :
      (LB.LinComb D.toPre.P.L (Y := D.toPre.P.A.left) (K := PEmpty) PEmpty.elim PEmpty.elim).U j0 ≤
      D.toPre.P.A.hom ⁻¹ᵁ ⊤) (pullU D.toPre.P.A.hom ⊤ c) := by
    have e1 : te.s j0 = res (le_of_eq (wchart_empty j0)) f := by
      simp only [f]
      exact (res_back _ _ _).symm
    rw [e1, hc, units_map_eq_res]
    erw [res_res']
    rfl
  have hzp : eSec D.toPre.P.A ≫ D.toPre.P.A.hom = 𝟙 _ := by
    exact Over.w η[D.toPre.P.A]
  have key : (LB.pullGen D.toPre.P.L _ _ te (eSec D.toPre.P.A)).s j0 = res le_top c := by
    show res _ (pullU _ _ (te.s j0)) = _
    rw [hte]
    exact pull_pull_id _ _ hzp _ _ c
  have hz1 : LB.Gen.Corr D.toPre.P.L _ _ (K' := PEmpty) PEmpty.elim PEmpty.elim
      (LB.pullGen D.toPre.P.L _ _ te (eSec D.toPre.P.A)) (LB.oneGen D.toPre.P.L) :=
    corr_trans hL (corr_pullGen (corr_symm c2) _) hv
  have hc1 : c = 1 := by
    have e := hz1 j0 j0 (fun k => k.elim) (fun k => k.elim) (fun k => k.elim)
    rw [key] at e
    change res _ (res _ c) = res _ (1 : Γ(Spec (CommRingCat.of V), _)ˣ) at e
    rw [map_one] at e
    erw [res_res'] at e
    exact eq_one_of_res_top _ (by ext y; simp [LB.wchart]) c e
  have hte1 : te.s j0 = 1 := by rw [hte, hc1, map_one, map_one]
  intro j hj
  have e := c2 j j0 hj (fun k => k.elim) (fun _ k => k.elim)
  rw [hte1] at e
  erw [map_one] at e
  have hle : LB.wchart D.toPre.P.L φ j ≤ LB.wchart D.toPre.P.L φ j ⊓ LB.wchart D.toPre.P.L PEmpty.elim j0 :=
    le_inf le_rfl (by rw [wchart_empty]; exact le_top)
  have e2 := congrArg (res hle) e
  erw [map_one, res_res', res_refl'] at e2
  exact e2
end ReciprocityTheory.ChartRestriction.G.DVR
