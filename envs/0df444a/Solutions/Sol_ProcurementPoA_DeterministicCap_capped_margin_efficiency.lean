-- Prove2me | solution 1 for ProcurementPoA.DeterministicCap.capped_margin_efficiency
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:23:08.243219+00:00
-- url     : https://prove2.me/submissions/f079a08c-f2ee-4ef9-8cbd-f481b6c32924
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_ProcurementPoA_DeterministicCap_ValueAuction_jin_lu_efficiency
import Theorems.Thm_ProcurementPoA_DeterministicCap_capped_to_value_auction

open MeasureTheory
open ProcurementPoA.DeterministicCap

theorem solution (R T : ℝ) (hR : 1 ≤ R) (hT : 1 ≤ T)
    {n : ℕ} (D : IndependentTypes n) (τ : TieRule n) (σ : MixedProfile n)
    (hcost : InCostInterval D 1 R) (heq : IsBNE D τ σ T) :
    ENNReal.ofReal (1 - epsilon) * ∫⁻ c, ENNReal.ofReal (T - lowest c) ∂(typeLaw D) ≤
      ∫⁻ x, (if lowest (fun i => (x i).2) ≤ T then
          ∑ i, ENNReal.ofReal (T - (x i).1) * τ.select (fun j => (x j).2) {i} else 0)
        ∂(playLaw D σ) := by
  obtain ⟨τ', σ', heq', hopt, hwelfare⟩ :=
    capped_to_value_auction R T hR hT D τ σ hcost heq
  have hJL := ValueAuction.jin_lu_efficiency D τ' σ' (T - 1)
    (fun _ c => max (T - c) 0) (by linarith)
    (fun _ => (measurable_const.sub measurable_id).max measurable_const)
    (by
      intro i c hc
      have hc1 : 1 ≤ c := (hcost i hc).1
      constructor
      · exact le_max_right _ _
      · exact max_le (by linarith) (by linarith))
    heq'
  rwa [hopt, hwelfare] at hJL
