-- Prove2me | solution 1 for P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGI_ptm__L_8c0085973b4b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:50:57.735547+00:00
-- url     : https://prove2.me/submissions/eb9f47e0-c2c8-4a98-80b5-867f83796a59

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartActionPoint
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GmHomAt
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGI_cc__L_a00542ceadc4
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGF_const_substPS
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGF_psJet_subst_trunc
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGH_ptm_congr
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGH_ptm_subst
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_power_series_in_fin_one
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGG_act__a_200fb8f04dea
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGG_const__a_6a1787d574a4


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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGI
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGH
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGI
theorem _root_.solution (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0)
    (hact : ∀ a j, MvPowerSeries.subst (fun p : Fin 1 × Fin C.d => φ p.2) (C.B.A.act a j) =
      MvPowerSeries.subst (actPS (Dw := Dw) c a) (φ j)) (m : ℕ) (k : 𝓞 E) :
    ptm C ![φa c φ k] m ≫ homAt y.x (jetSubstP m (σL C m)) = ptm C ![φa c φ k, φa c φ (H.w0 * k)] m := by
  have hP0 : ∀ j, MvPowerSeries.constantCoeff (φa c φ k j) = 0 := const_φa c φ hφ k
  have hP : ∀ i j, MvPowerSeries.constantCoeff ((![φa c φ k] : Fin 1 → _) i j) = 0 := by
    intro i j
    rw [Fin.fin_one_eq_zero i]
    exact hP0 j
  rw [ptm_subst C _ hP m _ (cc_σL C m)]
  set Q : Fin 1 × Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S :=
    fun p => (![φa c φ k] : Fin 1 → _) p.1 p.2 with hQdef
  have hQ : ∀ p, MvPowerSeries.constantCoeff (Q p) = 0 := fun p => hP p.1 p.2
  have hQe : Q = fun p => φa c φ k p.2 := by
    funext p
    obtain ⟨p1, p2⟩ := p
    rw [hQdef, Fin.fin_one_eq_zero p1]
    rfl
  refine ptm_congr C (fun i j => const_substPS Q hQ _ ?_) ?_ m ?_
  · rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPolynomial.coeff_coe]
    exact cc_σL C m (i, j)
  · rw [Fin.forall_fin_two]
    exact ⟨fun j => hP0 j, fun j => const_φa c φ hφ _ j⟩
  · rw [Fin.forall_fin_two]
    refine ⟨fun j => ?_, fun j => ?_⟩
    · simp only [σL, Matrix.cons_val_zero]
      rw [MvPolynomial.coe_X, MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero hQ), hQe]
    · simp only [σL, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [power_series_in_fin_one, psJet_subst_trunc m Q hQ, hQe, act_φa c hφ hact]
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGI
