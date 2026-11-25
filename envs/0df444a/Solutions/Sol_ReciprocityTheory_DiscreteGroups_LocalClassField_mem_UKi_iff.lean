-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.mem_UKi_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:06:42.53107+00:00
-- url     : https://prove2.me/submissions/03ad7197-3379-4194-acc0-efbe129f5924

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsE
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsF

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh
noncomputable section
variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (i : ℕ) (x : Kˣ) :
    x ∈ UKi p K i ↔ x ∈ UK p K ∧ ‖((x : K) : PadicAlgCl p) - 1‖ ≤ (p : ℝ) ^ (- (i : ℝ) / eK p K) := Iff.rfl
end ReciprocityTheory.DiscreteGroups.LocalClassField
