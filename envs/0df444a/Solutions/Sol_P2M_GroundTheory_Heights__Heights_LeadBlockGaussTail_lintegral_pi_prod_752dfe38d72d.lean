-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LeadBlockGaussTail_lintegral_pi_prod_752dfe38d72d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:02:32.545376+00:00
-- url     : https://prove2.me/submissions/93021823-63e8-4621-a3ee-325d36c4d5ad

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsLeadBlockGaussTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PLeadBlockGaussTail

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
open MeasureTheory Finset
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.LeadBlockGaussTail
namespace GroundTheory.Heights₂.Heights.LeadBlockGaussTail
theorem _root_.solution {E : Type*} [MeasurableSpace E] (μ : Measure E) [SigmaFinite μ] :
    ∀ (n : ℕ) (f : Fin n → E → ℝ≥0∞), (∀ i, Measurable (f i)) →
      ∫⁻ x, ∏ i, f i (x i) ∂Measure.pi (fun _ => μ) = ∏ i, ∫⁻ y, f i y ∂μ
  | 0, f, _ => by simp
  | n + 1, f, hf => by
      have e := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0
      let g : E × (Fin n → E) → ℝ≥0∞ := fun a => f 0 a.1 * ∏ i : Fin n, f i.succ (a.2 i)
      have hg : Measurable fun a : Fin n → E => ∏ i : Fin n, f i.succ (a i) :=
        Finset.measurable_prod _ fun i _ => (hf i.succ).comp (measurable_pi_apply i)
      calc ∫⁻ x, ∏ i, f i (x i) ∂Measure.pi (fun _ => μ)
          = ∫⁻ x, g (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E) 0 x)
              ∂Measure.pi (fun _ => μ) := by
            refine lintegral_congr fun x => ?_
            simp [g, Fin.prod_univ_succ, MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv]
            rfl
        _ = ∫⁻ a, g a ∂(μ.prod (Measure.pi fun _ : Fin n => μ)) :=
            e.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _) g
        _ = (∫⁻ y, f 0 y ∂μ) * ∫⁻ x, ∏ i : Fin n, f i.succ (x i) ∂(Measure.pi fun _ : Fin n => μ) :=
            lintegral_prod_mul (hf 0).aemeasurable hg.aemeasurable
        _ = ∏ i, ∫⁻ y, f i y ∂μ := by
            rw [solution μ n _ (fun i => hf i.succ), Fin.prod_univ_succ]
end GroundTheory.Heights₂.Heights.LeadBlockGaussTail
