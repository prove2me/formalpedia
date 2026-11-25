-- Prove2me | solution 1 for QPK.lintegral_pi_prod_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:02:49.808886+00:00
-- url     : https://prove2.me/submissions/85328f9a-ef2b-4aa1-b066-7817c164f941

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_LintegralFintypeProd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_WeilQuotientGlobalAssumptions
import Theorems.Thm_QPK_lintegral_fintype_prod


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open QPK
variable {ι : Type} [Fintype ι] {G : ι → Type} [∀ v, Group (G v)] [∀ v, MeasurableSpace (G v)]
  [∀ v, MeasurableMul₂ (G v)]
namespace QPK
theorem _root_.solution (μ ν : ∀ v, Measure (G v)) [∀ v, SigmaFinite (μ v)]
    [∀ v, SigmaFinite (ν v)] (φ : ∀ v, G v → ℝ≥0∞) (hφ : ∀ v, Measurable (φ v)) :
    ∫⁻ p, ∏ v, φ v (p.1 v * p.2 v) ∂((Measure.pi μ).prod (Measure.pi ν)) =
      ∏ v, ∫⁻ s, φ v s ∂(mulMap (μ v) (ν v)) := by
  have hm : Measurable (fun p : (∀ v, G v) × (∀ v, G v) => ∏ v, φ v (p.1 v * p.2 v)) :=
    Finset.measurable_prod _ fun v _ => (hφ v).comp
      (((measurable_pi_apply v).comp measurable_fst).mul ((measurable_pi_apply v).comp measurable_snd))
  rw [lintegral_prod _ hm.aemeasurable]
  have hin : ∀ x : (∀ v, G v), ∫⁻ y, ∏ v, φ v (x v * y v) ∂(Measure.pi ν) =
      ∏ v, ∫⁻ y, φ v (x v * y) ∂(ν v) := fun x =>
    lintegral_fintype_prod (fun v y => φ v (x v * y)) (fun v => (hφ v).comp (measurable_const_mul _))
  simp_rw [hin]
  rw [lintegral_fintype_prod (fun v x => ∫⁻ y, φ v (x * y) ∂(ν v))
    (fun v => ((hφ v).comp measurable_mul).lintegral_prod_right')]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [mulMap, lintegral_map (hφ v) measurable_mul,
    lintegral_prod (f := fun z : G v × G v => φ v (z.1 * z.2))
      (show Measurable (fun z : G v × G v => φ v (z.1 * z.2)) from
        (hφ v).comp measurable_mul).aemeasurable]
end QPK
