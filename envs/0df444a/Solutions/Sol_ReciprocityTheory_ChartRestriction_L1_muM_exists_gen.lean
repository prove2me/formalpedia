-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.muM_exists_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:38:55.196793+00:00
-- url     : https://prove2.me/submissions/bfd178bd-c545-447b-960e-d88c7d1baea0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_KurDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_MuMEvalPowEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open Formalism.L2.Th1.CM Polynomial
variable (l : ℕ) [Fact l.Prime]
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (n : ℕ) (hn : 0 < n) :
    ∃ g : ℂ_[l], g ^ n = 1 ∧ ∀ a : ℂ_[l], a ^ n = 1 → ∃ k : ℕ, g ^ k = a := by
  have : NeZero n := ⟨hn.ne'⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_monoid_generator (α := rootsOfUnity n ℂ_[l])
  refine ⟨((g : ℂ_[l]ˣ) : ℂ_[l]), ?_, fun a ha => ?_⟩
  · have := g.2
    rw [mem_rootsOfUnity'] at this
    exact this
  · obtain ⟨k, hk⟩ := hg (rootsOfUnity.mkOfPowEq a ha)
    refine ⟨k, ?_⟩
    have := congrArg (fun x : rootsOfUnity n ℂ_[l] => ((x : ℂ_[l]ˣ) : ℂ_[l])) hk
    simpa using this
end ReciprocityTheory.ChartRestriction.L1
