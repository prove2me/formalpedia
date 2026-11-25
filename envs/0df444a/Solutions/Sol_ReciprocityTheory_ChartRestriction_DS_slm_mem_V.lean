-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.slm_mem_V
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:25:32.664866+00:00
-- url     : https://prove2.me/submissions/78d07d36-b48a-430e-b1da-8e3612ca2888

import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CayleyChartDomainIsOpen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slm_Ji_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Matrix
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {ε : Fin n → Bool}
local notation "JJ" => Formalism.REAL.Jm
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {g0 : Matrix (Fin n) (Fin n) ℂ} (hg0 : Formalism.REAL.inUJ ε g0) : g0 ∈ slmV ε g0 := by
  have h1 : slmJi ε g0 * g0 = 1 := slm_Ji_mul hg0
  have hW : g0 ∈ cayleyChartDomain ε g0 := by
    show (slmJi ε g0 * g0 + 1).det ≠ 0
    rw [h1, ← two_smul ℂ (1 : Matrix (Fin n) (Fin n) ℂ), Matrix.det_smul, Matrix.det_one]
    simp
  have hX0 : slmX ε g0 g0 = 0 := by
    unfold slmX slmP
    rw [h1]
    simp
  show g0 ∈ cayleyChartDomain ε g0 ∧ (1 - slmX ε g0 g0).det ≠ 0
  refine ⟨hW, ?_⟩
  rw [hX0]
  simp
end ReciprocityTheory.ChartRestriction.DS
