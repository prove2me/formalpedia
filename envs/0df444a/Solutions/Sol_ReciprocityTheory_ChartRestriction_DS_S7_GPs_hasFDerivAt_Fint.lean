-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.GPs.hasFDerivAt_Fint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:54:01.421493+00:00
-- url     : https://prove2.me/submissions/2f59c5d1-3c6e-49b3-81aa-1ae550b8fbff

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GPs_emb_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GPs_hasFDerivAt_FD
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GPs_contOn_FD
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GPs_cont_int
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GPs_cont_FD
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GPs_int_int
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
open Finset MeasureTheory Matrix
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
open ReciprocityTheory.ChartRestriction.DS.S7.GPs
variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}
local notation "𝕄f" => Fin n → Fin n → ℂ
variable {g : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ → ℂ}
variable [CompactSpace (KG ε)]
namespace ReciprocityTheory.ChartRestriction.DS.S7.GPs
theorem _root_.solution (T : KType ε Λ) (hg : ContDiffOn ℂ ∞ g (Wset n)) {z : Matrix (Fin n) (Fin n) ℂ}
    (hz : z ∈ Ps1.Uset ε) :
    HasFDerivAt (fun x : 𝕄f => Fint T g x) (cK T • ∫ k, FD T g z k ∂(muK ε)) z := by
  unfold Fint
  refine HasFDerivAt.const_smul (f := fun x : 𝕄f => ∫ k, g (emb x k) • Pk T k ∂(muK ε)) ?_ (cK T)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (Ps1.isOpen_Uset (ε := ε)) z hz
  have hcb : Metric.closedBall z (r / 2) ⊆ Ps1.Uset ε :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hK : IsCompact (Metric.closedBall z (r / 2) ×ˢ (Set.univ : Set (KG ε))) :=
    (isCompact_closedBall z (r / 2)).prod isCompact_univ
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn ((contOn_FD T hg).mono (Set.prod_mono hcb le_rfl))
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F' := FD T g)
    (Metric.ball_mem_nhds (z : 𝕄f) (half_pos hr)) ?_ (int_int T hg hz) ?_ ?_ (integrable_const C) ?_
  · filter_upwards [(Ps1.isOpen_Uset (ε := ε)).mem_nhds hz] with y hy
    exact (cont_int T hg hy).aestronglyMeasurable
  · exact (cont_FD T hg hz).aestronglyMeasurable
  · exact ae_of_all _ fun k y hy => hC (y, k) ⟨Metric.ball_subset_closedBall hy, Set.mem_univ _⟩
  · exact ae_of_all _ fun k y hy => hasFDerivAt_FD T hg k (emb_mem (hcb (Metric.ball_subset_closedBall hy)) k)
end ReciprocityTheory.ChartRestriction.DS.S7.GPs
