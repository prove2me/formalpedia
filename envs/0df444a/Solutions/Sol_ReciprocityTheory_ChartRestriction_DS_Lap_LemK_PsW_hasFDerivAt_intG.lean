-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.LemK.PsW.hasFDerivAt_intG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:02:04.457566+00:00
-- url     : https://prove2.me/submissions/d11fb57a-fcf7-4694-87d2-d3013b0464b9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_TransferStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_PsWord
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_PsW_hasFDerivAt_G
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_PsW_continuousOn_G__8f575f8638c2
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_PsW_continuous_Gk
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_PsW_continuous_G_k_2cdb220cc1dc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_PsW_integrable_G
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_Ps1_isOpen_Uset


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix Topology
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.LemK
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open ReciprocityTheory.ChartRestriction.DS.Lap.LemK.PsW
variable {n : ℕ}
local notation "𝕄" => Fin n → Fin n → ℂ
local notation "MM" => Matrix (Fin n) (Fin n) ℂ
local notation "WW" => ((Fin n → Fin n → ℂ) × (Fin n → Fin n → ℂ)) × (Fin n → Fin n → ℂ)
variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}
namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK.PsW
theorem _root_.solution [CompactSpace (KG ε)] (T : KType ε Λ) (μ : Fin n → ℤ) (D : List MM)
    {z : 𝕄} (hz : z ∈ Ps1.Uset ε) :
    HasFDerivAt (fun x : 𝕄 => ∫ k, G T μ D x k ∂(muK ε)) (∫ k, G' T μ D z k ∂(muK ε)) z := by
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.isOpen_iff.1 Ps1.isOpen_Uset z hz
  have hr0 : 0 < ε₀ / 2 := half_pos hε₀
  have hcb : Metric.closedBall z (ε₀ / 2) ⊆ Ps1.Uset ε :=
    (Metric.closedBall_subset_ball (half_lt_self hε₀)).trans hball
  obtain ⟨C, hC⟩ := ((isCompact_closedBall z (ε₀ / 2)).prod isCompact_univ).exists_bound_of_continuousOn
    ((continuousOn_G' T μ D).mono (Set.prod_mono hcb le_rfl))
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ => C)
    (Metric.ball_mem_nhds z hr0) ?_
    (integrable_G T μ D hz) (continuous_G'k T μ D hz).aestronglyMeasurable ?_ (integrable_const C) ?_
  · exact Filter.eventually_of_mem (Ps1.isOpen_Uset.mem_nhds hz) fun x hx =>
      (continuous_Gk T μ D hx).aestronglyMeasurable
  · exact ae_of_all _ fun k x hx => hC (x, k) ⟨Metric.ball_subset_closedBall hx, Set.mem_univ _⟩
  · exact ae_of_all _ fun k x hx => hasFDerivAt_G T μ D k (hcb (Metric.ball_subset_closedBall hx) k)
end ReciprocityTheory.ChartRestriction.DS.Lap.LemK.PsW
