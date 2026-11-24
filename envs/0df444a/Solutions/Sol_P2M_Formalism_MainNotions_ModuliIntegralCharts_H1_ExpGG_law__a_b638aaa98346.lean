-- Prove2me | solution 1 for P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGG_law__a_b638aaa98346
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:00:09.053157+00:00
-- url     : https://prove2.me/submissions/5a99df04-76ab-4637-9cbd-12aaae07b442

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_JetSubstPSEqJetMap
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_UnitIdSt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_HasSubstActPS
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGG_const_actPS
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGG_actPS_add
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGF_const_substPS


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
theorem _root_.solution {d : ℕ} {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S} {uvec : Lt1 Dw → Fin d → S}
    {φ : Fin d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S} (hφ : IsExpOf F uvec φ) (u v : 𝓞 E) (j : Fin d) :
    subst (fun p : Fin 2 × Fin d => φa c φ (![u, v] p.1) p.2) (F j) = φa c φ (u + v) j := by
  let b : Fin 2 × Fin (dL Dw) → MvPowerSeries (Fin 1 × Fin (dL Dw)) S :=
    fun p => actPS (Dw := Dw) (S := S) c (![u, v] p.1) ((0 : Fin 1), p.2)
  have hb : HasSubst b := hasSubst_of_constantCoeff_zero (fun p => const_actPS c _ _)
  have hX : ∀ i : Fin 2, HasSubst (fun q : Fin 1 × Fin (dL Dw) =>
      (MvPowerSeries.X (i, q.2) : MvPowerSeries (Fin 2 × Fin (dL Dw)) S)) :=
    fun i => hasSubst_of_constantCoeff_zero (fun q => by simp)
  have hA : HasSubst (fun p : Fin 2 × Fin d => atPt p.1 (φ p.2)) :=
    hasSubst_of_constantCoeff_zero (fun p => ExpGF.const_substPS _ (fun q => by simp) _ (hφ.const p.2))
  have hS : HasSubst (fun q : Fin 1 × Fin (dL Dw) =>
      (MvPowerSeries.X ((0 : Fin 2), q.2) + MvPowerSeries.X ((1 : Fin 2), q.2) :
        MvPowerSeries (Fin 2 × Fin (dL Dw)) S)) :=
    hasSubst_of_constantCoeff_zero (fun q => by simp)
  have key := congrArg (MvPowerSeries.subst b) (hφ.hom j)
  rw [subst_comp_subst_apply hA hb, subst_comp_subst_apply hS hb] at key
  have e1 : (fun p : Fin 2 × Fin d => MvPowerSeries.subst b (atPt p.1 (φ p.2))) =
      fun p => φa c φ (![u, v] p.1) p.2 := by
    funext ⟨i, k⟩
    simp only [atPt, φa]
    rw [subst_comp_subst_apply (hX i) hb]
    congr 1
    funext ⟨q1, q2⟩
    rw [subst_X hb]
    have h1 : q1 = 0 := Subsingleton.elim _ _
    subst h1
    rfl
  have e2 : (fun q : Fin 1 × Fin (dL Dw) => MvPowerSeries.subst b
      (MvPowerSeries.X ((0 : Fin 2), q.2) + MvPowerSeries.X ((1 : Fin 2), q.2) :
        MvPowerSeries (Fin 2 × Fin (dL Dw)) S)) = actPS (Dw := Dw) (S := S) c (u + v) := by
    funext ⟨q1, q2⟩
    have h1 : q1 = 0 := Subsingleton.elim _ _
    subst h1
    rw [subst_add hb, subst_X hb, subst_X hb]
    exact actPS_add c u v _
  rw [e1, e2] at key
  exact key
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG
