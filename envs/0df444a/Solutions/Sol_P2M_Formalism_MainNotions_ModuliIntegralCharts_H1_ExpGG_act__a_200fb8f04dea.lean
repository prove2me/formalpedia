-- Prove2me | solution 1 for P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGG_act__a_200fb8f04dea
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:07:08.049335+00:00
-- url     : https://prove2.me/submissions/ffe19211-2536-40d5-adaf-1cfac439b459

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_JetSubstPSEqJetMap
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_UnitIdSt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_HasSubstActPS
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGG_hasSubst_actPS
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGG__a_mul_3f365165b132

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG
open MvPowerSeries NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {S : Type} [CommRing S] (c : Coeff l) [Algebra c.F S]
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG
theorem _root_.solution {d : ℕ} {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S}
    {φ : Fin d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S} (hφ : ∀ j, constantCoeff (φ j) = 0)
    (hact : ∀ a j, subst (fun p : Fin 1 × Fin d => φ p.2) (act a j) = subst (actPS (Dw := Dw) c a) (φ j))
    (a u : 𝓞 E) (j : Fin d) :
    subst (fun p : Fin 1 × Fin d => φa c φ u p.2) (act a j) = φa c φ (a * u) j := by
  have hP : HasSubst (fun p : Fin 1 × Fin d => φ p.2) :=
    hasSubst_of_constantCoeff_zero (fun p => hφ p.2)
  have h := subst_comp_subst_apply hP (hasSubst_actPS (Dw := Dw) (S := S) c u) (act a j)
  rw [hact a j] at h
  exact h.symm.trans (φa_mul c φ a u j)
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG
