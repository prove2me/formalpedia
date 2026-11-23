-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.expandsAt_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:28:29.309745+00:00
-- url     : https://prove2.me/submissions/cda34229-6f74-48d7-ade0-f8e6c922e4bf

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExpPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_gs_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mem_finf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_exp_germ
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
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (e k : ℕ)
variable (σ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α)
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution (h : U.ExpandsAt e k σ f) : ∃ S : Finset D.toPre.X, ∀ (Z : Scheme.{0})
    (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J), Good D.toPre.P.L z J →
      (∀ α ∉ S, sval (f α) (r ≫ (pGl U e)) z J = 0) ∧ ∀ jL, (fGl I G e) (r z) ∈ U.LG.L.U jL →
      (wv U e r z (J (r ≫ (pGl U e))) jL ^ k).val * sv U k σ (r ≫ (fGl I G e)) z jL =
        ∑ α ∈ S, sval (f α) (r ≫ (pGl U e)) z J * (val (tG U e α) r z J).val := by
  obtain ⟨S, h₀, h₁⟩ := h
  refine ⟨S, fun Z r z J hJ => ⟨fun α hα => ?_, fun jL hL => ?_⟩⟩
  · have m := hJ.mem (D.toPre.famφB α) (r ≫ (pGl U e))
    exact (gs_pull r _ z _ m _).symm.trans ((congrArg (gs r z _) (h₀ α hα _)).trans (gs_zero r z _ m))
  · have hz : r z ∈ U.expW e (fun _ => J (r ≫ (pGl U e)), fun _ => jL) (fun _ => jL) S
        (fun α a => J ((r ≫ (pGl U e)) ≫ D.toPre.famφB α a)) (fun α a => J (r ≫ Oφl U e α a)) :=
      ⟨⟨⟨mem_pull.2 (hJ (r ≫ (pGl U e))), mem_pull.2 hL⟩, Set.mem_iInter.2 fun _ => hL⟩,
        mem_finf S _ _ fun α _ => ⟨hJ.mem (D.toPre.famφB α) (r ≫ (pGl U e)), hJ.mem _ r⟩⟩
    obtain ⟨k₁, k₂⟩ := exp_germ U e k σ f r z S _ jL _ _ hz
    refine k₁.symm.trans ((congrArg (gs r z _) (h₁ (fun _ => J (r ≫ (pGl U e)), fun _ => jL) (fun _ => jL) _ _ rfl
      ?_)).trans k₂)
    have c : ∀ a, Sum.elim (fun _ : PUnit.{1} => J (r ≫ (pGl U e)))
        (Sum.elim (fun a : S × Fin 4 => J ((r ≫ (pGl U e)) ≫ D.toPre.famφB a.1.1 a.2))
          (fun a : S × Fin 4 => J (r ≫ Oφl U e a.1.1 a.2))) a =
        J (r ≫ Sum.elim (fun _ : PUnit.{1} => (pGl U e))
          (Sum.elim (fun a : S × Fin 4 => (pGl U e) ≫ D.toPre.famφB a.1.1 a.2)
            (fun a : S × Fin 4 => Oφl U e a.1.1 a.2)) a) := by
      rintro (a | a | a)
      exacts [rfl, congrArg J (Category.assoc _ _ _), rfl]
    exact fun a b hab => (c a).trans ((congrArg (fun q => J (r ≫ q)) hab).trans (c b).symm)
end ReciprocityTheory.ChartRestriction.G.DVR
