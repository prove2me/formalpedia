-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.logNormSec_eq_indicator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:06:43.932642+00:00
-- url     : https://prove2.me/submissions/0bfb2c75-3535-43f5-99e4-8cb245ad43d3

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LogInt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LogInt
import Theorems.Thm_ReciprocityTheory_AnForm_M_logNormSecLocal

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
open scoped ContDiff
noncomputable section
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}
    {L : LocPot X} {s : X → X → ℂ} (hS : IsSection A L s) {x p : X} (hp : p ∈ L.U x) :
    logNormSec L s p = Real.log ‖s x p‖ - L.φ x p + {q | s x q = 0}.indicator (L.φ x) p := by
  by_cases h0 : s x p = 0
  · unfold logNormSec
    rw [hS.2 p x p ⟨L.mem_U p, hp⟩, Set.indicator_apply,
      if_pos (show p ∈ {q | s x q = 0} from h0), h0]
    simp
  · rw [Set.indicator_apply, if_neg (show p ∉ {q | s x q = 0} from h0),
      logNormSecLocal A L s x p hS hp h0]
    ring
end ReciprocityTheory.AnForm.M
