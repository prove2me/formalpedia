-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.box_product_weight_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:54:00.563208+00:00
-- url     : https://prove2.me/submissions/5227814a-54df-4e74-a2ad-b73f6b32754b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExpPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mem_finf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_box_q
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_rp__e27165827f88
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {j : ℕ} {D D' : DegData R I}
  {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  {pD : IsPowDeg D'.toPre D.toPre j} {pA : IsPowPolAV A' A j} {pG : IsPowGrp G' G j}
  {U' : Unif I D' A' G'} {U : Unif I D A G}
set_option maxHeartbeats 800000
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution (P : UnifPowOf3 pD pA pG U' U) {e : ℕ} {y : (thickObj R I e G').left} {J : ((thickObj R I e G').left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι}
    {J' : ((thickObj R I e G').left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι}
    (hJ : Good D.toPre.P.L y J) (hJ' : Good D'.toPre.P.L y J') {jL : Fin j → U.LG.L.ι} {jL' : U'.LG.L.ι}
    (hL : ∀ i, (pG.pr i).left (fGl I G' e y) ∈ U.LG.L.U (jL i)) (hL' : fGl I G' e y ∈ U'.LG.L.U jL') :
    omB pD y J J' (pGl U'.toUnifPre e) * wv U'.toUnifPre e (𝟙 _) y (J' (pGl U'.toUnifPre e)) jL' =
        (∏ i, wv U.toUnifPre e (rhoE I pG e i) y (J ((pGl U'.toUnifPre e) ≫ (pD.pw.pr i).left)) (jL i)) *
          gm (fGl I G' e) y ((LB.div (boxLB U.LG.L pG.pr) U'.LG.L).U (jL, jL')) (P.wL.s (jL, jL')) := by
  have hρ : ∀ i, rhoE I pG e i ≫ fGl I G e = fGl I G' e ≫ (pG.pr i).left := fun i => pullback.lift_fst _ _ _
  have hL₁ : ∀ i, fGl I G e (rhoE I pG e i y) ∈ U.LG.L.U (jL i) := fun i =>
    (congrArg (fun g => g y ∈ U.LG.L.U (jL i)) (hρ i)).mpr (hL i)
  have mL : fGl I G' e y ∈ (LB.div (boxLB U.LG.L pG.pr) U'.LG.L).U (jL, jL') := ⟨Set.mem_iInter.2 hL, hL'⟩
  have hq := box_q P e
  have mM : (pGl U'.toUnifPre e) y ∈ (LB.div (boxLB D.toPre.P.L pD.pw.pr) D'.toPre.P.L).U (fun i => J ((pGl U'.toUnifPre e) ≫ (pD.pw.pr i).left), J' (pGl U'.toUnifPre e)) :=
    ⟨Set.mem_iInter.2 fun i => hJ ((pGl U'.toUnifPre e) ≫ (pD.pw.pr i).left), hJ' (pGl U'.toUnifPre e)⟩
  have mW : ∀ i, rhoE I pG e i y ∈ (D.toPre.P.L.pull (pGl U.toUnifPre e)).U (fun _ => J ((pGl U'.toUnifPre e) ≫ (pD.pw.pr i).left)) ⊓
      (U.LG.L.pull (fGl I G e)).U (fun _ => jL i) := fun i =>
    ⟨mem_pull.2 ((congrArg (fun g => g y ∈ D.toPre.P.L.U (J ((pGl U'.toUnifPre e) ≫ (pD.pw.pr i).left))) (hq i)).mp (hJ _)),
      mem_pull.2 (hL₁ i)⟩
  have hm : (𝟙 _ : (thickObj R I e G').left ⟶ _) y ∈ (pGl U'.toUnifPre e) ⁻¹ᵁ (LB.div (boxLB D.toPre.P.L pD.pw.pr) D'.toPre.P.L).U
      (fun i => J ((pGl U'.toUnifPre e) ≫ (pD.pw.pr i).left), J' (pGl U'.toUnifPre e)) ⊓
      (LB.div (D'.toPre.P.L.pull (pGl U'.toUnifPre e)) (U'.LG.L.pull (fGl I G' e))).U (fun _ => J' (pGl U'.toUnifPre e), fun _ => jL') ⊓
      (⨅ i, rhoE I pG e i ⁻¹ᵁ (LB.div (D.toPre.P.L.pull (pGl U.toUnifPre e)) (U.LG.L.pull (fGl I G e))).U
        (fun _ => J ((pGl U'.toUnifPre e) ≫ (pD.pw.pr i).left), fun _ => jL i)) ⊓
      (fGl I G' e) ⁻¹ᵁ (LB.div (boxLB U.LG.L pG.pr) U'.LG.L).U (jL, jL') :=
    ⟨⟨⟨mM, mem_pull.2 (hJ' (pGl U'.toUnifPre e)), mem_pull.2 hL'⟩, by
      rw [← Finset.inf_univ_eq_iInf]; exact mem_finf _ _ _ fun i _ => mW i⟩, mL⟩
  have W := congrArg (gm (𝟙 _) y _) (P.w_pr e (fun i => J ((pGl U'.toUnifPre e) ≫ (pD.pw.pr i).left)) (J' (pGl U'.toUnifPre e)) jL' jL)
  exact ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_rp₁ (pGl U'.toUnifPre e) y _ _ _ hm _) (gm_res (𝟙 _) y _ hm _))).symm.trans (W.trans
        ((map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_prod _ _ _).trans (Finset.prod_congr rfl fun i _ =>
          gm_rp₁ (rhoE I pG e i) y _ _ _ hm _)) (gm_rp₁ (fGl I G' e) y _ _ _ hm _))))
end ReciprocityTheory.ChartRestriction.G.DVR
