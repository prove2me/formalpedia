-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.expandsAt_of_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:28:30.032317+00:00
-- url     : https://prove2.me/submissions/dba5bb94-e655-47e8-a249-1ff6f7351cd6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExpPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_gs_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_exp_germ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_good
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sval_of
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_of


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
theorem _root_.solution (S : Finset D.toPre.X) (h : ∀ (y : (thickObj R I e G).left) (J), Good D.toPre.P.L y J →
    (∀ α ∉ S, sval (f α) (pGl U e) y J = 0) ∧ ∀ jL, (fGl I G e) y ∈ U.LG.L.U jL →
      (wv U e (𝟙 _) y (J (pGl U e)) jL ^ k).val * sv U k σ (fGl I G e) y jL =
        ∑ α ∈ S, sval (f α) (pGl U e) y J * (val (tG U e α) (𝟙 _) y J).val) : U.ExpandsAt e k σ f := by
  refine ⟨S, fun α hα j => fn_ext fun y hy => ?_, ?_⟩
  · choose J hJ using fun ψ : (thickObj R I e G).left ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (ψ y)
    refine (gs_pull (𝟙 _) _ y _ hy _).trans (Eq.trans ?_ (gs_zero (𝟙 _) y _ hy).symm)
    rw [Category.id_comp]
    exact (sec_trans (f α) _ y hy (Good.mem hJ _ _)).trans ((congrArg _ ((h y J hJ).1 α hα)).trans (mul_zero _))
  · rintro ⟨p₁, p₂⟩ j₁ jf jt hj hc
    obtain rfl : j₁ = fun _ => p₂ PUnit.unit := funext fun i => (congrArg j₁ (Subsingleton.elim i 0)).trans hj
    refine fn_ext fun y hy => ?_
    obtain ⟨k₁, k₂⟩ := exp_germ U e k σ f (𝟙 _) y S (p₁ PUnit.unit) (p₂ PUnit.unit) jf jt hy
    obtain ⟨J, hJ, eJ⟩ := exists_good D.toPre.P.L D.toPre.P.isLB y _ _ hc (by
      rintro (a | a | a)
      exacts [mem_pull.1 hy.1.1.1, Set.mem_iInter.1 (U.expW_le_f e _ _ jf jt a.1.2 hy) a.2,
        Set.mem_iInter.1 (U.expWeight_le_chart_weight e _ _ jf jt a.1.2 hy) a.2])
    have H := (h y J hJ).2 (p₂ PUnit.unit) (mem_pull.1 hy.1.1.2)
    have e₀ : J (pGl U e) = p₁ PUnit.unit := eJ (.inl PUnit.unit)
    rw [e₀] at H
    rw [Category.id_comp] at k₁ k₂
    refine k₁.trans (H.trans (Eq.trans (Finset.sum_congr rfl fun α hα => ?_) k₂.symm))
    rw [sval_of (f α) _ y J (jf α) (fun a => eJ (.inr (.inl (⟨α, hα⟩, a)))),
      val_of (tG U e α) _ y J (jt α) (fun a => by rw [Category.id_comp]; exact eJ (.inr (.inr (⟨α, hα⟩, a))))]
end ReciprocityTheory.ChartRestriction.G.DVR
