-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AnalyticLimit_ArgumentConvergenceLemmas_exists_bound_iteratedFDeriv_a8446911247a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:39:33.063809+00:00
-- url     : https://prove2.me/submissions/fc555868-c2e0-4159-9fa0-da082a3f7454

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMoll
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_RegularizedMaxC2ExampleRealLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_IsOpenKappaOpenNeighbourhood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_NormIteratedFDerivCompLeOfIsOpen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.AnalyticLimit
open GroundTheory.Heights₂.Heights.AnalyticLimit.ArgumentConvergenceLemmas
open Filter Topology Metric Set MeasureTheory
open scoped ContDiff
open ReciprocityTheory.AnForm.A (Mollifier molli shrink)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (errE errorWithLinear ell)
noncomputable section
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
namespace GroundTheory.Heights₂.Heights.AnalyticLimit.ArgumentConvergenceLemmas
theorem _root_.solution {f : E → F} {s K : Set E} (hs : IsOpen s)
    (hf : ContDiffOn ℝ 2 f s) (hK : IsCompact K) (hKs : K ⊆ s) :
    ∃ B : ℝ, ∀ i : ℕ, i ≤ 2 → ∀ y ∈ K, ‖iteratedFDeriv ℝ i f y‖ ≤ B := by
  have h : ∀ i : ℕ, i ≤ 2 → ∃ B : ℝ, ∀ y ∈ K, ‖iteratedFDeriv ℝ i f y‖ ≤ B := fun i hi =>
    hK.exists_bound_of_continuousOn
      ((ContinuousOn.continuousOn_iteratedFDeriv hf hs (by exact_mod_cast hi)).mono hKs)
  obtain ⟨B0, h0⟩ := h 0 (by norm_num)
  obtain ⟨B1, h1⟩ := h 1 (by norm_num)
  obtain ⟨B2, h2⟩ := h 2 le_rfl
  refine ⟨max B0 (max B1 B2), fun i hi y hy => ?_⟩
  interval_cases i
  · exact (h0 y hy).trans (le_max_left _ _)
  · exact (h1 y hy).trans ((le_max_left _ _).trans (le_max_right _ _))
  · exact (h2 y hy).trans ((le_max_right _ _).trans (le_max_right _ _))
end GroundTheory.Heights₂.Heights.AnalyticLimit.ArgumentConvergenceLemmas
