-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.CasPsB.hasFDerivAt_integral_K
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:14:13.697046+00:00
-- url     : https://prove2.me/submissions/bc0dedc6-98f4-4a44-893d-4f53bea35f55

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasPsA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasPsB

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
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
open ReciprocityTheory.ChartRestriction.DS.S7.CasPsB
local notation "𝕄" => Fin n → Fin n → ℂ
variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}
namespace ReciprocityTheory.ChartRestriction.DS.S7.CasPsB
theorem _root_.solution [CompactSpace (KG ε)] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] [SecondCountableTopologyEither (KG ε) E]
    [SecondCountableTopologyEither (KG ε) (𝕄 →L[ℂ] E)] {U : Set (Matrix (Fin n) (Fin n) ℂ)} (hU : IsOpen U)
    (F : Matrix (Fin n) (Fin n) ℂ → KG ε → E) (F' : Matrix (Fin n) (Fin n) ℂ → KG ε → (𝕄 →L[ℂ] E))
    (hF : ContinuousOn (fun p : Matrix (Fin n) (Fin n) ℂ × KG ε => F p.1 p.2) (U ×ˢ Set.univ))
    (hF' : ContinuousOn (fun p : Matrix (Fin n) (Fin n) ℂ × KG ε => F' p.1 p.2) (U ×ˢ Set.univ))
    (hd : ∀ x ∈ U, ∀ k, HasFDerivAt (fun y : 𝕄 => F y k) (F' x k) x)
    {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ U) :
    HasFDerivAt (fun x : 𝕄 => ∫ k, F x k ∂(muK ε)) (∫ k, F' z k ∂(muK ε)) z := by
  have : IsFiniteMeasureOnCompacts (muK ε) := by unfold muK; infer_instance
  have : IsFiniteMeasure (muK ε) := inferInstance
  have hcont : ∀ x ∈ U, Continuous (F x) := fun x hx =>
    hF.comp_continuous (continuous_const.prodMk continuous_id) (fun _ => ⟨hx, trivial⟩)
  have hcont' : ∀ x ∈ U, Continuous (F' x) := fun x hx =>
    hF'.comp_continuous (continuous_const.prodMk continuous_id) (fun _ => ⟨hx, trivial⟩)
  have hU' : IsOpen (U : Set 𝕄) := hU
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU' z hz
  have hδ : (0 : ℝ) < r / 2 := half_pos hr
  have hcl : Metric.closedBall (z : 𝕄) (r / 2) ⊆ (U : Set 𝕄) :=
    (Metric.closedBall_subset_ball (half_lt_self hr)).trans hball
  have hK : IsCompact (Metric.closedBall (z : 𝕄) (r / 2) ×ˢ (Set.univ : Set (KG ε))) :=
    (isCompact_closedBall _ _).prod isCompact_univ
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hF'.mono (Set.prod_mono hcl le_rfl))
  have hin : ∀ x ∈ Metric.ball (z : 𝕄) (r / 2), x ∈ (U : Set 𝕄) :=
    fun x hx => hcl (Metric.ball_subset_closedBall hx)
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ => C)
    (F' := fun x k => F' x k)
    (Metric.ball_mem_nhds (z : 𝕄) hδ)
    (Filter.eventually_of_mem (Metric.ball_mem_nhds (z : 𝕄) hδ)
      fun x hx => (hcont x (hin x hx)).aestronglyMeasurable)
    (integrableOn_univ.mp ((hcont z hz).continuousOn.integrableOn_compact isCompact_univ))
    (hcont' z hz).aestronglyMeasurable
    (Filter.Eventually.of_forall fun k x hx => hC (x, k) ⟨Metric.ball_subset_closedBall hx, trivial⟩)
    (integrable_const C)
    (Filter.Eventually.of_forall fun k x hx => hd x (hin x hx) k)
end ReciprocityTheory.ChartRestriction.DS.S7.CasPsB
