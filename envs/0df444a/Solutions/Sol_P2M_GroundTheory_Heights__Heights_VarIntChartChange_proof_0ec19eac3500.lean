-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_VarIntChartChange_proof_0ec19eac3500
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:19:11.638331+00:00
-- url     : https://prove2.me/submissions/df6bec35-812a-46a6-a310-e90a06efc61d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarIntChartChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartChangeSheetNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartChangeLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLinearNoetherNormalization
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPosPartSplit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PIntegralIndependent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PVarIntChartChange
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartChange_posPart_eq_ae901a283544
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IntegralIndep_chartInt_eq_posParts_786379f5608c


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Matrix ComplexSets
noncomputable section
open ChartChange
namespace GroundTheory.Heights₂.Heights
namespace VarIntChartChange
theorem _root_.solution (hN : ComplexSets.LinearNoetherNormalization.Statement)
    (hNull : ChartChangeSheetNull.Statement) (hL : ChartChangeLocal.Statement) :
    VarIntChartChange.Statement := by
  intro n d J J' u u' U U' Φ Ψ f f' φ φ' c g hJ hd hJ' hd' hu hu' hU hU' hZU hZU' hΦ hΨ hΦm hΨm
    hΨΦ hΦΨ hf hf' hff hφ hφ' hg hg0 hφφ hint
  have hex : ∃ A : Matrix (Fin d) (Fin n) ℂ, IsFiniteProjection J A := hN n d J hd
  have hex' : ∃ A : Matrix (Fin d) (Fin n) ℂ, IsFiniteProjection J' A := hN n d J' hd'
  have hA := hex.choose_spec
  have hA' := hex'.choose_spec
  simp only [varInt, dif_pos hex, dif_pos hex']
  have hpos := posPart_eq hNull hL hJ hd hJ' hd' hu hu' hA hA' hU hU' hZU hZU' hΦ hΨ hΦm hΨm hΨΦ
    hΦΨ hf hf' hff hφ hφ' hg hg0 hφφ
  have hneg := posPart_eq hNull hL hJ hd hJ' hd' hu hu' hA hA' hU hU' hZU hZU' hΦ hΨ hΦm hΨm hΨΦ
    hΦΨ hf.neg hf'.neg (fun x hx => by simp only [Pi.neg_apply, hff x hx]) hφ hφ' hg hg0 hφφ
  obtain ⟨h1, h2⟩ := IntegralIndep.chartInt_eq_posParts hA hf φ
  obtain ⟨h1', h2'⟩ := IntegralIndep.chartInt_eq_posParts hA' hf' φ'
  have hI := hint _ hA
  have hI' : Integrable (chartAbsDens J' hex'.choose f' φ') := h1'.2 (by rw [hpos, hneg]; exact h1.1 hI)
  rw [h2 hI, h2' hI', hpos, hneg]
end VarIntChartChange
end GroundTheory.Heights₂.Heights
