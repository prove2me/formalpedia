-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.pow_pow_succ_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:48:14.89955+00:00
-- url     : https://prove2.me/submissions/6eb99109-d7d5-41b2-afbb-3b6b4cbf1011

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_MemOfPowQKSubOne
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_PowPowSuccSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
open _root_.Neutral.B1 ReciprocityTheory.DiscreteGroups.LocalClassField Polynomial
variable {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
theorem _root_.solution {R : Type*} [Monoid R] {q n : ℕ} (hq : 0 < q) {c : R} (h : c ^ (q ^ n - 1) = 1) :
    c ^ (q ^ n) = c := by
  have h1 : 1 ≤ q ^ n := Nat.one_le_pow _ _ hq
  have : q ^ n = (q ^ n - 1) + 1 := by omega
  rw [this, pow_succ, h, one_mul]
end ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
