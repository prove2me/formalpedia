-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.IdA.hasDerivAt_intK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:15:04.001403+00:00
-- url     : https://prove2.me/submissions/7a89bc0f-f24a-4c90-a2b5-93a9772678b2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCasA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IdThmA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℝ}
open ReciprocityTheory.ChartRestriction.DS.S7.IdA
namespace ReciprocityTheory.ChartRestriction.DS.S7.IdA
theorem _root_.solution [CompactSpace (KG ε)] (T : KType ε Λ) (F F' : ℂ → KG ε → (T.V →L[ℂ] T.V))
    {S : Set ℂ} (hS : IsOpen S)
    (hF : ContinuousOn (fun p : ℂ × KG ε => F p.1 p.2) (S ×ˢ Set.univ))
    (hF' : ContinuousOn (fun p : ℂ × KG ε => F' p.1 p.2) (S ×ˢ Set.univ))
    (hd : ∀ s ∈ S, ∀ k, HasDerivAt (fun s => F s k) (F' s k) s) {s0 : ℂ} (hs0 : s0 ∈ S) :
    HasDerivAt (fun s => ∫ k, F s k ∂(muK ε)) (∫ k, F' s0 k ∂(muK ε)) s0 := by
  have : IsFiniteMeasureOnCompacts (muK ε) := by unfold muK; infer_instance
  have : IsFiniteMeasure (muK ε) := inferInstance
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hS s0 hs0
  have hcl : Metric.closedBall s0 (r / 2) ⊆ S :=
    (Metric.closedBall_subset_ball (half_lt_self hr)).trans hball
  have hK : IsCompact (Metric.closedBall s0 (r / 2) ×ˢ (Set.univ : Set (KG ε))) :=
    (isCompact_closedBall s0 _).prod isCompact_univ
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hF'.mono (Set.prod_mono hcl le_rfl))
  have hin : ∀ s ∈ Metric.ball s0 (r / 2), s ∈ S := fun s hs => hcl (Metric.ball_subset_closedBall hs)
  have hc : ∀ s ∈ S, Continuous (F s) := fun s hs =>
    hF.comp_continuous (continuous_const.prodMk continuous_id) fun _ => ⟨hs, trivial⟩
  have hc' : Continuous (F' s0) :=
    hF'.comp_continuous (continuous_const.prodMk continuous_id) fun _ => ⟨hs0, trivial⟩
  have hi : Integrable (F s0) (muK ε) :=
    integrableOn_univ.mp ((hc s0 hs0).continuousOn.integrableOn_compact isCompact_univ)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun _ => C)
    (Metric.ball_mem_nhds s0 (half_pos hr))
    (Filter.eventually_of_mem (Metric.ball_mem_nhds s0 (half_pos hr))
      fun s hs => (hc s (hin s hs)).aestronglyMeasurable)
    hi hc'.aestronglyMeasurable
    (Filter.Eventually.of_forall fun k s hs => hC (s, k) ⟨Metric.ball_subset_closedBall hs, trivial⟩)
    (integrable_const C)
    (Filter.Eventually.of_forall fun k s hs => hd s (hin s hs) k)).2
end ReciprocityTheory.ChartRestriction.DS.S7.IdA
