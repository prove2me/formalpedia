-- Prove2me | solution 1 for ThreeSum.SubsetAddress.enumerationWork_bound
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:50:01.564567+00:00
-- url     : https://prove2.me/submissions/c1d3512d-d908-4355-8c84-82a4fecbdb0b

import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

section


/-!
# Compact addresses for bounded-cardinality bit masks

Both ranking and enumeration recurse on the highest available bit. The
enumerator stops immediately when the requested layer is empty. In
particular, it does not enumerate the ambient Boolean cube and filter it.
-/

namespace ThreeSum.SubsetAddress

set_option maxRecDepth 4000

open Finset
open scoped BigOperators
















































































































































































































theorem enumerationWork_bound_sourceProof (L k : ℕ) :
    enumerationWork L k ≤ (4 * L + 1) * L.choose k + 1 := by
  induction L generalizing k with
  | zero => cases k <;> simp [enumerationWork]
  | succ L ih =>
      cases k with
      | zero => simp [enumerationWork]
      | succ k =>
          by_cases hk : k + 1 ≤ L + 1
          · have hi := ih (k + 1)
            have hj := ih k
            have hp := Nat.choose_pos hk
            rw [Nat.choose_succ_succ] at hp
            simp only [enumerationWork, if_pos hk, enumerateLayer_length,
              Nat.choose_succ_succ]
            nlinarith
          · simp [enumerationWork, hk, Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hk)]




































































































































































































































end ThreeSum.SubsetAddress

end


theorem solution : ∀ (L k : Nat),
  @LE.le.{0} Nat instLENat (ThreeSum.SubsetAddress.enumerationWork L k)
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) L)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (L.choose k))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) := by
  exact @ThreeSum.SubsetAddress.enumerationWork_bound_sourceProof

#print axioms solution
