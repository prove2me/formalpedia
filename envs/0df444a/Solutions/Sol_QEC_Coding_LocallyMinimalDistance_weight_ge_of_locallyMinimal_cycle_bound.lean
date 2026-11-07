-- Prove2me | solution 1 for QEC.Coding.LocallyMinimalDistance.weight_ge_of_locallyMinimal_cycle_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:57:07.491265+00:00
-- url     : https://prove2.me/submissions/66534b60-bfcf-47e7-a8c8-41235c17d478

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.Order.Lattice.Nat
import Definitions.Def_QEC_Coding_ExpanderCodes_LocallyMinimalDistance
import Theorems.Thm_QEC_Coding_LocallyMinimalDistance_exists_nonzero_locallyMinimal_cycle

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.LocallyMinimalDistance
universe u v
variable {C : Type*} [AddCommGroup C]
namespace QEC.Coding.LocallyMinimalDistance
theorem _root_.solution
    (weight : C → Nat) (Z B : AddSubgroup C) (moves : Finset C)
    (hBZ : B ≤ Z) (hmoves : ∀ m ∈ moves, m ∈ B)
    (lowerBound : Nat)
    (hlocal : ∀ c : C, c ∈ Z → c ≠ 0 →
      IsLocallyMinimal weight moves c → lowerBound ≤ weight c)
    (c : C) (hcZ : c ∈ Z) (hcB : c ∉ B) :
    lowerBound ≤ weight c := by
  obtain ⟨c', hc'Z, hc'0, hc'local, hc'le⟩ :=
    exists_nonzero_locallyMinimal_cycle weight Z B moves hBZ hmoves c hcZ hcB
  exact (hlocal c' hc'Z hc'0 hc'local).trans hc'le
end QEC.Coding.LocallyMinimalDistance
