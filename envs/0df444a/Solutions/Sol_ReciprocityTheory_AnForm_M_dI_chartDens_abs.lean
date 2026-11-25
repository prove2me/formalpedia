-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.dI_chartDens_abs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:07:11.356797+00:00
-- url     : https://prove2.me/submissions/fd7ab048-74b5-4769-89a9-a847e4180724

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Degree
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_DegreeIntA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution (A : FinHolAtlas e X) {D : Fin A.n → (Fin e → ℂ) → ℝ}
    (hD : DIChartDens A D) : DIChartDens A (fun a z => |D a z|) := by
  intro a b z hz hzb
  beta_reduce
  rw [hD a b z hz hzb, abs_mul, abs_pow, abs_norm]
end ReciprocityTheory.AnForm.M
