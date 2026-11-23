-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.exp_germ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:22:48.2888+00:00
-- url     : https://prove2.me/submissions/aba0b7f7-7fe8-4340-a4ab-f1c03581e596

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExpPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_gs_fsum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res


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
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (e k : ℕ)
variable (σ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α)
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution {Z : Scheme.{0}} (r : Z ⟶ (thickObj R I e G).left) (z : Z) (S : Finset D.toPre.X) (jM : D.toPre.P.L.ι)
    (jL : U.LG.L.ι) (jf jt : D.toPre.X → Fin 4 → D.toPre.P.L.ι)
    (hz : r z ∈ U.expW e (fun _ => jM, fun _ => jL) (fun _ => jL) S jf jt) :
    gs r z _ ((res (inf_le_left.trans inf_le_left : U.expW e (fun _ => jM, fun _ => jL) (fun _ => jL) S jf jt ≤
        (LB.div (D.toPre.P.L.pull (pGl U e)) (U.LG.L.pull (fGl I G e))).U (fun _ => jM, fun _ => jL))
        ((U.w e).s (fun _ => jM, fun _ => jL))).val ^ k *
      ((thickObj R I e G).left.presheaf.map (homOfLE (inf_le_left.trans inf_le_right :
        U.expW e (fun _ => jM, fun _ => jL) (fun _ => jL) S jf jt ≤
          (fGl I G e) ⁻¹ᵁ LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => jL))).op).hom
        (((fGl I G e).app _).hom (σ.f (fun _ => jL)))) =
      (wv U e r z jM jL ^ k).val * sv U k σ (r ≫ (fGl I G e)) z jL ∧
    gs r z _ (∑ α ∈ S.attach, ((thickObj R I e G).left.presheaf.map
        (homOfLE (U.expW_le_f e (fun _ => jM, fun _ => jL) (fun _ => jL) jf jt α.2)).op).hom
        (((pGl U e).app _).hom ((f α.1).f (jf α.1))) *
        (res (U.expWeight_le_chart_weight e (fun _ => jM, fun _ => jL) (fun _ => jL) jf jt α.2) ((tG U e α.1).s (jt α.1))).val) =
      ∑ α ∈ S, gs (r ≫ (pGl U e)) z (LB.wchart D.toPre.P.L (D.toPre.famφB α) (jf α)) ((f α).f (jf α)) *
        (gm r z (LB.wchart D.toPre.P.L (Oφl U e α) (jt α)) ((tG U e α).s (jt α))).val := by
  constructor
  · refine (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) ?_ ((gs_res r z _ hz _).trans (gs_pull r _ z _ hz.1.2 _)))
    rw [← Units.val_pow_eq_pow_val, gs_unit r z _ hz, map_pow]
    exact congrArg (fun u => (u ^ k).val) (gm_res r z _ hz _)
  · refine (gs_fsum r z _ hz _ _).trans (Eq.trans (Finset.sum_congr rfl fun α _ => ?_) (Finset.sum_attach S _))
    have l₁ := U.expW_le_f e (fun _ => jM, fun _ => jL) (fun _ => jL) jf jt α.2
    have l₂ := U.expWeight_le_chart_weight e (fun _ => jM, fun _ => jL) (fun _ => jL) jf jt α.2
    have a₁ := (gs_res r z l₁ hz (((pGl U e).app _).hom ((f α.1).f (jf α.1)))).trans
      (gs_pull r (pGl U e) z (LB.wchart D.toPre.P.L (D.toPre.famφB α.1) (jf α.1)) (l₁ hz) ((f α.1).f (jf α.1)))
    have a₂ := (gs_unit r z _ hz (res l₂ ((tG U e α.1).s (jt α.1)))).trans (congrArg Units.val (gm_res r z l₂ hz _))
    exact (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) a₁ a₂)
end ReciprocityTheory.ChartRestriction.G.DVR
