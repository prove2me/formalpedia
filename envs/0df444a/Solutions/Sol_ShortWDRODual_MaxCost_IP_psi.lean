-- Prove2me | solution 1 for ShortWDRODual.MaxCost.IP_psi
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T10:10:18.798369+00:00
-- url     : https://prove2.me/submissions/355363b0-ec76-417c-bb5b-eee0273ba2d7

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_ShortWDRODual_MaxCost_Setting
import Theorems.Thm_ShortWDRODual_MaxCost_example_2_proj
import Theorems.Thm_ShortWDRODual_MaxCost_example_2_sel
import Theorems.Thm_ShortWDRODual_IP_proj_selStar_imp_IP

open MeasureTheory ModelRiskOT.Duality ShortWDRODual.MaxCost
open scoped ENNReal

theorem solution {X : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X]
    [BorelSpace X] (Phat : Measure X) [IsProbabilityMeasure Phat]
    (f : X → ℝ) (hf : Measurable f)
    (c : X → X → ℝ) (hc : Continuous (fun q : X × X => c q.1 q.2))
    (hcnn : ∀ x y, 0 ≤ c x y) (hc0 : ∀ x, c x x = 0)
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ShortWDRODual.Legendre.IP Phat (psi c f ρ) := by
  have hProj := example_2_proj Phat
  have hSel := example_2_sel Phat
  -- (Sel) implies (Sel*): push `ℙ̂` forward along `x̂ ↦ (x̂, T x̂)`.
  have hSelStar : ShortWDRODual.IP.SelStar Phat := by
    intro E hE
    obtain ⟨hEval, hgraph, -⟩ := hE
    obtain ⟨T, hT, hTE⟩ := hSel E hEval hgraph
    have hTae : AEMeasurable T Phat := hT.aemeasurable
    have hF : AEMeasurable (fun xh => (xh, T xh)) Phat := aemeasurable_id.prodMk hTae
    refine ⟨Phat.map (fun xh => (xh, T xh)), ⟨Measure.isProbabilityMeasure_map hF, ?_⟩, ?_⟩
    · rw [AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable hF]
      have : (Prod.fst ∘ fun xh => (xh, T xh)) = id := rfl
      rw [this, Measure.map_id]
    · rw [Measure.map_apply_of_aemeasurable hF hgraph.compl]
      have : (fun xh => (xh, T xh)) ⁻¹' (ShortWDRODual.IP.graph E)ᶜ = ∅ := by
        ext xh
        simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false,
          not_not]
        exact hTE xh
      rw [this, measure_empty]
  have hmeas : Measurable (psi c f ρ) := by
    unfold psi
    exact Measurable.ite (measurableSet_lt measurable_const hc.measurable) measurable_const
      ((measurable_coe_real_ereal.comp hf).comp measurable_snd)
  have hdiag : ∀ xh x, psi c f ρ (xh, x) ≤ psi c f ρ (x, x) := by
    intro xh x
    have h0 : ¬ ρ < c x x := by rw [hc0]; exact not_lt.mpr hρ
    simp only [psi, h0, if_false]
    split_ifs
    · exact bot_le
    · exact le_refl _
  have hne : ∀ p, psi c f ρ p ≠ ⊤ := by
    intro p
    simp only [psi]
    split_ifs
    · exact bot_ne_top
    · exact EReal.coe_ne_top _
  exact ShortWDRODual.IP.proj_selStar_imp_IP Phat hProj hSelStar (psi c f ρ) ⟨hmeas, hdiag⟩ hne
