-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.mollify_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:58:24.328413+00:00
-- url     : https://prove2.me/submissions/a01eaa40-703a-4eda-a0a0-21bd4aebae00

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollB
import Theorems.Thm_ReciprocityTheory_AnForm_A_isOpen_shrink
import Theorems.Thm_ReciprocityTheory_AnForm_A_le_molli
import Theorems.Thm_ReciprocityTheory_AnForm_A_molli_le_polyMax
import Theorems.Thm_ReciprocityTheory_AnForm_A_molli_contDiffAt
import Theorems.Thm_ReciprocityTheory_AnForm_A_molli_submean

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Metric Filter Topology Set Real
open scoped ContDiff
noncomputable section
variable {D : ℕ}
variable (ρ : Mollifier D) {U : Set (Fin D → ℂ)} {φ : (Fin D → ℂ) → ℝ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution (hU : IsOpen U) (hφ : IsPsh U φ) {ε : ℝ} (hε : 0 < ε) :
    IsOpen (shrink U ε) ∧ ContDiffOn ℝ ∞ (molli ρ ε φ) (shrink U ε) ∧
      IsPsh (shrink U ε) (molli ρ ε φ) ∧
      ∀ z ∈ shrink U ε, φ z ≤ molli ρ ε φ z ∧ molli ρ ε φ z ≤ polyMax φ z ε := by
  have hcont : ContinuousOn (molli ρ ε φ) (shrink U ε) := fun z hz =>
    (molli_contDiffAt ρ hU hφ hε hz).continuousAt.continuousWithinAt
  refine ⟨isOpen_shrink hU hε, fun z hz => (molli_contDiffAt ρ hU hφ hε hz).contDiffWithinAt,
    ⟨hcont.upperSemicontinuousOn, fun z w hd => ⟨?_, molli_submean ρ hU hφ hε hd⟩⟩,
    fun z hz => ⟨le_molli ρ hU hφ hε hz, molli_le_polyMax ρ hU hφ hε hz⟩⟩
  refine ContinuousOn.circleIntegrable' ?_
  refine hcont.comp (by fun_prop : Continuous fun ζ : ℂ => z + ζ • w).continuousOn fun ζ hζ => ?_
  exact hd ζ (by simp at hζ; linarith)
end ReciprocityTheory.AnForm.A
