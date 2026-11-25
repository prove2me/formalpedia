-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.integrable_iteratedFDeriv_translate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:47:25.312194+00:00
-- url     : https://prove2.me/submissions/08228832-40bb-447f-ba13-a715cc8ff947

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_IteratedFDerivMulConstOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_IntegrableIteratedFDerivTranslate
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_continuousOn_iteratedFDeriv_translate
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_integrable_of_continuous_K


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution (F : M2 n → ℂ) (U : Set (M2 n)) (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U)
    {Kg : Type} [TopologicalSpace Kg] [CompactSpace Kg] [MeasurableSpace Kg] [BorelSpace Kg]
    (μ : Measure Kg) [IsFiniteMeasureOnCompacts μ] (ι : Kg → M2 n) (hι : Continuous ι) (c : Kg → ℂ) (hc : Continuous c)
    (N : ℕ) (x : M2 n) (hx : ∀ k, ι k * x ∈ U) (w : Fin N → M2 n) :
    Integrable (fun k => iteratedFDeriv ℂ N (fun y => F (ι k * y) * c k) x w) μ := by
  have h := continuousOn_iteratedFDeriv_translate F U hU hF Kg ι hι c hc N
  have hg : Continuous (fun k : Kg => (k, x)) := continuous_id.prodMk continuous_const
  have hm : ∀ k, (k, x) ∈ (Set.univ ×ˢ {x | ∀ k, ι k * x ∈ U} : Set (Kg × M2 n)) :=
    fun k => ⟨Set.mem_univ _, hx⟩
  have h2 : Continuous (fun k : Kg => iteratedFDeriv ℂ N (fun y => F (ι k * y) * c k) x) :=
    h.comp_continuous hg hm
  exact integrable_of_continuous_K μ ((continuous_eval_const w).comp h2)
end PositivityTheory.Rg.Sw.LVs
