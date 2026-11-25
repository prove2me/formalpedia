-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.Ps1.hasFDerivAt_intG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:44:22.238115+00:00
-- url     : https://prove2.me/submissions/bdcdace5-3835-490a-a7aa-d8a83e627e91

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_Ps1_isOpen_Uset
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_Ps1_hasFDerivAt_Gint
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_Ps1_continuousOn_GintD
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_Ps1_continuous_Gint
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_Ps1_continuous_GintD
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_Ps1_integrable_Gint

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
variable {n : ℕ}
open ReciprocityTheory.ChartRestriction.DS.S7.Ps1
local notation "𝕄" => Fin n → Fin n → ℂ
variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}
namespace ReciprocityTheory.ChartRestriction.DS.S7.Ps1
theorem _root_.solution [CompactSpace (KG ε)] (T : KType ε Λ) (μ : Fin n → ℤ)
    {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ Uset ε) :
    HasFDerivAt (fun x : 𝕄 => ∫ k, Gint T μ x k ∂(muK ε)) (∫ k, GintD T μ z k ∂(muK ε)) z := by
  have : IsFiniteMeasureOnCompacts (muK ε) := by unfold muK; infer_instance
  have : IsFiniteMeasure (muK ε) := inferInstance
  have hU : IsOpen (Uset ε : Set 𝕄) := isOpen_Uset
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU z hz
  have hδ : (0 : ℝ) < r / 2 := half_pos hr
  have hcl : Metric.closedBall (z : 𝕄) (r / 2) ⊆ (Uset ε : Set 𝕄) :=
    (Metric.closedBall_subset_ball (half_lt_self hr)).trans hball
  have hK : IsCompact (Metric.closedBall (z : 𝕄) (r / 2) ×ˢ (Set.univ : Set (KG ε))) :=
    (isCompact_closedBall _ _).prod isCompact_univ
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    ((continuousOn_GintD T μ).mono (Set.prod_mono hcl le_rfl))
  have hin : ∀ x ∈ Metric.ball (z : 𝕄) (r / 2), x ∈ (Uset ε : Set 𝕄) :=
    fun x hx => hcl (Metric.ball_subset_closedBall hx)
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ => C)
    (F' := fun x k => GintD T μ x k)
    (Metric.ball_mem_nhds (z : 𝕄) hδ)
    (Filter.eventually_of_mem (Metric.ball_mem_nhds (z : 𝕄) hδ)
      fun x hx => (continuous_Gint T μ (hin x hx)).aestronglyMeasurable)
    (integrable_Gint T μ hz) (continuous_GintD T μ hz).aestronglyMeasurable
    (Filter.Eventually.of_forall fun k x hx => hC (x, k) ⟨Metric.ball_subset_closedBall hx, trivial⟩)
    (integrable_const C)
    (Filter.Eventually.of_forall fun k x hx => hasFDerivAt_Gint T μ k (hin x hx k))
end ReciprocityTheory.ChartRestriction.DS.S7.Ps1
