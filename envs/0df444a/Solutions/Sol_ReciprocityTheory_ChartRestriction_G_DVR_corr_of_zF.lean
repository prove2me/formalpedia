-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.corr_of_zF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:32:35.474741+00:00
-- url     : https://prove2.me/submissions/42d197ef-c404-4e60-adca-cbcc62e83bc6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_CartesianLiftThreeCompProjection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBCorr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_bf_units_const
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_res_back
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_units_map_eq_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_eq_one_of_res_top
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_shape_ratio
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_res_res__b0a8af1c3378
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_corr_mulGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_corr_pullGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_corr_pullGen_invGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_corr_pullGen_mulGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_corr_ratio_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_corr_refl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_corr_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_corr_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_fsum_empty
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_fsum_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_fsum_sumElim
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_gen_transport
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_invGen_isGen_of_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen_of_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen_of_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pull_pull_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_sameSum_iff_fsum
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
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi IsLocalRing
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F]
  {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]
open scoped Classical
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution (hGF : GlobalFnsSt) (hBC : PolBaseChangeSt) (hL : D.toPre.P.L.IsLB)
    {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → ((DegPre.BF D.toPre F).left ⟶ D.toPre.P.A.left)} {ε : K → ℤ}
    {φ' : K' → ((DegPre.BF D.toPre F).left ⟶ D.toPre.P.A.left)} {ε' : K' → ℤ}
    (t : LB.Gen (LB.LinComb D.toPre.P.L φ ε)) (ht : t.IsGen)
    (t' : LB.Gen (LB.LinComb D.toPre.P.L φ' ε')) (ht' : t'.IsGen) (hs : LB.SameSum φ ε φ' ε')
    (hval : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L φ ε t (DegPre.zF D.toPre F).left)
      (LB.pullGen D.toPre.P.L φ' ε' t' (DegPre.zF D.toPre F).left)) :
    LB.Gen.Corr D.toPre.P.L φ ε φ' ε' t t' := by
  have hs' : LB.SameSum φ' ε' φ ε := by rw [sameSum_iff_fsum] at hs ⊢; exact hs.symm
  obtain ⟨t'', ht'', c1⟩ := gen_transport hL hs' t' ht'
  set ρ := LB.mulGen D.toPre.P.L _ _ _ _ t (LB.invGen D.toPre.P.L φ ε t'')
  have hρ : ρ.IsGen := mulGen_isGen_of_isGen _ ht _ (invGen_isGen_of_isGen _ ht'')
  have hs0 : LB.SameSum (Sum.elim φ φ) (Sum.elim ε (fun k => -ε k)) (K' := PEmpty) PEmpty.elim PEmpty.elim := by
    rw [sameSum_iff_fsum, fsum_sumElim, fsum_neg, add_neg_cancel, fsum_empty]
  obtain ⟨te, -, c2⟩ := gen_transport hL hs0 ρ hρ
  let j0 : PEmpty → D.toPre.P.L.ι := PEmpty.elim
  let f : Γ((DegPre.BF D.toPre F).left, ⊤)ˣ := res (le_of_eq (wchart_empty j0).symm) (te.s j0)
  obtain ⟨c, hc⟩ := bf_units_const D F hGF hBC f

  have hz1 : LB.Gen.Corr D.toPre.P.L _ _ (K' := PEmpty) PEmpty.elim PEmpty.elim
      (LB.pullGen D.toPre.P.L _ _ te (DegPre.zF D.toPre F).left) (LB.oneGen D.toPre.P.L) := by
    have a1 := corr_pullGen (corr_symm c2) (DegPre.zF D.toPre F).left
    have a2 := corr_pullGen_mulGen t (LB.invGen D.toPre.P.L φ ε t'') (DegPre.zF D.toPre F).left
    have a3 := corr_mulGen (corr_refl _ (pullGen_isGen_of_isGen _ _ t ht (DegPre.zF D.toPre F).left))
      (corr_pullGen_invGen t'' (DegPre.zF D.toPre F).left)
    have a4 : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L φ ε t (DegPre.zF D.toPre F).left)
        (LB.pullGen D.toPre.P.L φ ε t'' (DegPre.zF D.toPre F).left) :=
      corr_trans hL hval (corr_pullGen c1 _)
    exact corr_trans hL a1 (corr_trans hL a2 (corr_trans hL a3 (corr_ratio_one a4)))
  have hte : te.s j0 = res (fun _ _ => trivial :
      (LB.LinComb D.toPre.P.L (Y := (DegPre.BF D.toPre F).left) (K := PEmpty) PEmpty.elim PEmpty.elim).U j0 ≤
      (fst (TF (R := V) F) D.toPre.P.A).left ⁻¹ᵁ ⊤) (pullU (fst (TF (R := V) F) D.toPre.P.A).left ⊤ c) := by
    have e1 : te.s j0 = res (le_of_eq (wchart_empty j0)) f := by
      simp only [f]
      exact (res_back _ _ _).symm
    rw [e1, hc, units_map_eq_res]
    erw [res_res']
    rfl
  have hzp : (DegPre.zF D.toPre F).left ≫ (fst (TF (R := V) F) D.toPre.P.A).left = 𝟙 _ := by
    rw [← Over.comp_left, zF_fst]; rfl
  have key : (LB.pullGen D.toPre.P.L _ _ te (DegPre.zF D.toPre F).left).s j0 = res le_top c := by
    show res _ (pullU _ _ (te.s j0)) = _
    rw [hte]
    exact pull_pull_id _ _ hzp _ _ c
  have hc1 : c = 1 := by
    have e := hz1 j0 j0 (fun k => k.elim) (fun k => k.elim) (fun k => k.elim)
    rw [key] at e
    change res _ (res _ c) = res _ (1 : Γ((TF (R := V) F).left, _)ˣ) at e
    rw [map_one] at e
    erw [res_res'] at e
    exact eq_one_of_res_top _ (by ext y; simp [LB.wchart]) c e
  have hf1 : f = 1 := by rw [hc, hc1, map_one]
  have hte1 : te.s j0 = 1 := by
    simp only [f] at hf1
    rw [← res_back (le_of_eq (wchart_empty j0)) (le_of_eq (wchart_empty j0).symm) (te.s j0), hf1, map_one]
    rfl

  have hf1 : f = 1 := by rw [hc, hc1, map_one]
  have htt : LB.Gen.Corr D.toPre.P.L φ ε φ ε t t'' := by
    intro j j₂ hj hj₂ hm
    let J : K ⊕ K → D.toPre.P.L.ι := Sum.elim j j₂
    have hJ : LB.Coh D.toPre.P.L (Sum.elim φ φ) J := by
      rintro (k₁ | k₁) (k₂ | k₂) e
      · exact hj k₁ k₂ e
      · exact hm k₁ k₂ e
      · exact (hm k₂ k₁ e.symm).symm
      · exact hj₂ k₁ k₂ e
    have e := c2 J j0 hJ (fun k => k.elim) (fun _ k' => k'.elim)
    have le : LB.wchart D.toPre.P.L φ j ⊓ LB.wchart D.toPre.P.L φ j₂ ≤ LB.wchart D.toPre.P.L (Sum.elim φ φ) J :=
      fun y hy => Set.mem_iInter.2 fun k => by
        rcases k with k | k
        · exact Set.mem_iInter.1 hy.1 k
        · exact Set.mem_iInter.1 hy.2 k
    rw [hte1] at e
    exact shape_ratio _ _ _ (t.s j) (t''.s j₂) _ e _ _ (le_inf le (fun _ _ => by rw [wchart_empty]; trivial))
  exact corr_trans hL htt (corr_symm c1)
end ReciprocityTheory.ChartRestriction.G.DVR
