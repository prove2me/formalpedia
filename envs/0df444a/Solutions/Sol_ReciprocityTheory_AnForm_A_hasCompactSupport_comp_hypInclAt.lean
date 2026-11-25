-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.hasCompactSupport_comp_hypInclAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:04:18.055965+00:00
-- url     : https://prove2.me/submissions/b0bc19cf-1abf-4fc4-954e-72dc576b6cb2

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContDiffOfContDiffOnZeroOff
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LogInt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenCoord
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HasCompactSupportCompHypInclAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution (i : Fin (n + 1)) {h : (Fin (n + 1) → ℂ) → ℝ}
    (hhc : HasCompactSupport h) : HasCompactSupport (fun w : Fin n → ℂ => h (hypInclAt i w)) := by
  have hr : Continuous (fun z : Fin (n + 1) → ℂ => Fin.removeNth i z) :=
    continuous_pi fun j => continuous_apply _
  have hK : IsCompact ((fun z : Fin (n + 1) → ℂ => Fin.removeNth i z) '' tsupport h) := hhc.image hr
  unfold HasCompactSupport
  refine IsCompact.of_isClosed_subset hK (isClosed_tsupport _) ?_
  refine closure_minimal ?_ hK.isClosed
  intro w hw
  exact ⟨hypInclAt i w, subset_tsupport _ hw, by simp [hypInclAt, Fin.removeNth_insertNth]⟩
end ReciprocityTheory.AnForm.A
