-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.Kn_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:40:09.579492+00:00
-- url     : https://prove2.me/submissions/4b855204-0b70-406a-a490-338866582b62

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
variable (K)
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
theorem _root_.solution {n : ℕ} {S : IntermediateField ℚ_[p] (PadicAlgCl p)} (h1 : K ≤ S)
    (h2 : ∀ ζ : PadicAlgCl p, ζ ^ (qK p K ^ n - 1) = 1 → ζ ∈ S) : Kn p K n ≤ S :=
  sup_le h1 (IntermediateField.adjoin_le_iff.2 h2)
end ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
