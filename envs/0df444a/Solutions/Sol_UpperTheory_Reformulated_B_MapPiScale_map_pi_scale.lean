-- Prove2me | solution 1 for UpperTheory.Reformulated.B.MapPiScale.map_pi_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:33:33.055492+00:00
-- url     : https://prove2.me/submissions/4ab3f1ea-fc14-41b2-9d52-8a1e9afe76cb

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MapPiScale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

open MeasureTheory
namespace UpperTheory.Reformulated.B.MapPiScale
theorem _root_.solution :
    ∀ {ι : Type} [inst : Fintype ι] {α : ι → Type}
    [inst_1 : (i : ι) → MeasurableSpace (α i)] (μ : (i : ι) → MeasureTheory.Measure (α i))
    [∀ (i : ι), MeasureTheory.SigmaFinite (μ i)] (g : (i : ι) → α i → α i),
    (∀ (i : ι), Measurable (g i)) →
      ∀ (c : ι → ENNReal),
        (∀ (i : ι), c i ≠ (0 : ENNReal)) →
          (∀ (i : ι), c i ≠ ⊤) →
            (∀ (i : ι), MeasureTheory.Measure.map (g i) (μ i) = c i • μ i) →
              MeasureTheory.Measure.map (fun (x : (i : ι) → α i) (i : ι) ↦ g i (x i)) (MeasureTheory.Measure.pi μ) =
                (∏ i : ι, c i) • MeasureTheory.Measure.pi μ := by
  intro ι _ α _ μ _ g hg c _ hc h
  have hs : ∀ i, SigmaFinite ((μ i).map (g i)) := by
    intro i
    rw [h i, ← ENNReal.coe_toNNReal (hc i)]
    exact (inferInstance : SigmaFinite ((c i).toNNReal • μ i))
  rw [Measure.pi_map_pi (fun i => (hg i).aemeasurable)]
  refine Measure.pi_eq fun s _ => ?_
  simp only [h, Measure.smul_apply, smul_eq_mul, Measure.pi_pi, Finset.prod_mul_distrib]
end UpperTheory.Reformulated.B.MapPiScale
