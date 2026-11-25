-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.diag_apply_of_weight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:22:19.546453+00:00
-- url     : https://prove2.me/submissions/8af0cca0-7a50-489d-859a-129c74308fa0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_LayerSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (hE : IsGlRep E) {ω : Fin n → ℝ} {w : M}
    (hw : ∀ c, E c c w = (ω c : ℂ) • w) (a b c : Fin n) :
    E c c (E a b w) = ((ω + root a b) c : ℂ) • E a b w := by
  have h := congrArg (fun T : Module.End ℂ M => T w) (hE c c a b)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  have h2 : E c c (E a b w) = E a b (E c c w) +
      ((if c = a then E c b else 0) w - (if b = c then E a c else 0) w) := by
    rw [← h]
    abel
  have e1 : (if c = a then E c b else 0) w = ((if c = a then 1 else 0 : ℝ) : ℂ) • E a b w := by
    by_cases h' : c = a
    · subst h'
      simp
    · simp [h']
  have e2 : (if b = c then E a c else 0) w = ((if c = b then 1 else 0 : ℝ) : ℂ) • E a b w := by
    by_cases h' : b = c
    · subst h'
      simp
    · simp [h', Ne.symm h']
  rw [h2, hw c, map_smul, e1, e2]
  simp only [root, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
  push_cast
  module
end ReciprocityTheory.ChartRestriction.DS
