-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.cca_contDiffOn_nat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:43:52.697041+00:00
-- url     : https://prove2.me/submissions/8f1f6782-46c9-4794-8a3f-440c65321aea

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasChainA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_cca_differentiableOn_fderiv_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Metric Set Filter Topology MeasureTheory Complex
open scoped ContDiff Real
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution [FiniteDimensional ℂ X] [CompleteSpace E] {U : Set X} (hU : IsOpen U) :
    ∀ (k : ℕ) {F : X → E}, DifferentiableOn ℂ F U → ContDiffOn ℂ k F U := by
  intro k
  induction k with
  | zero => intro F hF; exact contDiffOn_zero.2 hF.continuousOn
  | succ k ih =>
    intro F hF
    have hk : ContDiffOn ℂ k (fderiv ℂ F) U := by
      rw [contDiffOn_clm_apply]
      intro u
      exact ih (cca_differentiableOn_fderiv_apply hU hF u)
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hU]
    first
      | exact ⟨hF, fun h => absurd h (by simp), hk⟩
      | exact ⟨hF, hk⟩
end ReciprocityTheory.ChartRestriction.DS.S7
