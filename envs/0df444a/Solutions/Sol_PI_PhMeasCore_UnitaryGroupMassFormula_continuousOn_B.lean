-- Prove2me | solution 1 for PI.PhMeasCore.UnitaryGroupMassFormula.continuousOn_B
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:04:21.925808+00:00
-- url     : https://prove2.me/submissions/d721fde6-5d7a-4ae3-a215-1fccfb362279

import Definitions.Def_Formalism_PeriodIntegrals_PhMeasCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SmoothTranslationMeasure_Development

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Filter Topology
open scoped InnerProductSpace ContDiff
noncomputable section
open PI PI.PhMeasCore PI.PhMeasCore.UnitaryGroupMassFormula
open PI.PhMeasCore
namespace PI.PhMeasCore.UnitaryGroupMassFormula
theorem _root_.solution {n : ℕ} {Hm : Matrix (Fin n) (Fin n) ℂ} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {Wp : Type} [NormedAddCommGroup Wp]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {B : H → Wp} {w : H}
    (hS : StepSub) (hW : StepWord) (hmul : MulOnUH Hm σ)
    (hexp : ∀ X, InLie Hm X → ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ UH Hm)
    (hadd : ∀ v ∈ smoothVecs Hm σ, ∀ v' ∈ smoothVecs Hm σ, B (v + v') = B v + B v')
    (hB : IsCWCont Hm σ B) (hw : w ∈ smoothVecs Hm σ) :
    ContinuousOn (fun g => B (σ g w)) (UH Hm) := by
  obtain ⟨C, Ws, hWs, hBd⟩ := hB
  have hS' := hS n Hm H σ w hmul hw
  have hsub : ∀ v ∈ smoothVecs Hm σ, ∀ v' ∈ smoothVecs Hm σ, B (v - v') = B v - B v' := by
    intro v hv v' hv'
    have h := hadd (v - v') (hS'.2 v hv v' hv') v' hv'
    rw [sub_add_cancel] at h
    rw [h, add_sub_cancel_right]
  intro g₀ hg₀
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Filter.Tendsto
      (fun g => C * (Ws.map fun ws => ‖dsigW σ ws (σ g w) - dsigW σ ws (σ g₀ w)‖).sum)
      (nhdsWithin g₀ (UH Hm)) (nhds 0) := by
    have h := Filter.Tendsto.const_mul C (tendsto_list_sum (f := fun ws g => ‖dsigW σ ws (σ g w) - dsigW σ ws (σ g₀ w)‖)
      (a := fun ws => ‖dsigW σ ws (σ g₀ w) - dsigW σ ws (σ g₀ w)‖) Ws fun ws hws =>
      Filter.Tendsto.norm (Filter.Tendsto.sub
        ((hW n Hm H σ w hmul hexp hw ws (hWs ws hws)).1 g₀ hg₀) tendsto_const_nhds))
    convert h using 2
    simp
  refine squeeze_zero' (Filter.Eventually.of_forall fun g => norm_nonneg _) ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with g hg
  have h1 := hS'.1 g hg
  have h0 := hS'.1 g₀ hg₀
  rw [← hsub _ h1 _ h0]
  refine (hBd _ (hS'.2 _ h1 _ h0)).trans (le_of_eq ?_)
  congr 2
  refine List.map_congr_left fun ws hws => ?_
  rw [(hW n Hm H σ w hmul hexp hw ws (hWs ws hws)).2 g hg g₀ hg₀]
end PI.PhMeasCore.UnitaryGroupMassFormula
