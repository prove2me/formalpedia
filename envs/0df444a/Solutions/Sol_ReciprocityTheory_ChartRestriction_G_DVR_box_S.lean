-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.box_S
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:02:11.989915+00:00
-- url     : https://prove2.me/submissions/5c6ca928-a37e-4379-98a4-3ee3e5e58bbe

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExpPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_gs_prod

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
theorem _root_.solution (P : UnifPowOf3 pD pA pG U' U) {e k : ℕ} {y : (thickObj R I e G').left} {σ : Fin j → H0 U.LG.L k} {σ' : H0 U'.LG.L k}
    (hσ' : IsBoxSecG pG P.wL k σ' σ) {jL : Fin j → U.LG.L.ι} {jL' : U'.LG.L.ι}
    (hL : ∀ i, (pG.pr i).left (fGl I G' e y) ∈ U.LG.L.U (jL i)) (hL' : fGl I G' e y ∈ U'.LG.L.U jL') :
    (gm (fGl I G' e) y ((LB.div (boxLB U.LG.L pG.pr) U'.LG.L).U (jL, jL')) (P.wL.s (jL, jL')) ^ k).val *
        sv U'.toUnifPre k σ' (fGl I G' e) y jL' = ∏ i, sv U.toUnifPre k (σ i) (rhoE I pG e i ≫ fGl I G e) y (jL i) := by
  have hρ : ∀ i, rhoE I pG e i ≫ fGl I G e = fGl I G' e ≫ (pG.pr i).left := fun i => pullback.lift_fst _ _ _
  have hL₁ : ∀ i, fGl I G e (rhoE I pG e i y) ∈ U.LG.L.U (jL i) := fun i =>
    (congrArg (fun g => g y ∈ U.LG.L.U (jL i)) (hρ i)).mpr (hL i)
  have mL : fGl I G' e y ∈ (LB.div (boxLB U.LG.L pG.pr) U'.LG.L).U (jL, jL') := ⟨Set.mem_iInter.2 hL, hL'⟩
  have Sg := congrArg (gs (fGl I G' e) y ((LB.div (boxLB U.LG.L pG.pr) U'.LG.L).U (jL, jL'))) (hσ' jL jL')
  rw [gs_mul _ y _ mL, gs_unit _ y _ mL, map_pow] at Sg
  refine (congrArg₂ (· * ·) rfl (gs_res (fGl I G' e) y (boxG_le_b pG jL jL') mL _).symm).trans
    (Sg.trans ((gs_prod _ y _ mL _ _).trans (Finset.prod_congr rfl fun i _ => ?_)))
  rw [hρ]
  exact (gs_res (fGl I G' e) y (boxG_le_c pG jL jL' i) mL _).trans
    (gs_pull (fGl I G' e) (pG.pr i).left y _ (boxG_le_c pG jL jL' i mL) _)
end ReciprocityTheory.ChartRestriction.G.DVR
