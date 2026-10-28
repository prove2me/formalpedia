-- Prove2me | solution 1 for RuntimeTransfer.packing_oracle_transfer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T11:26:15.15046+00:00
-- url     : https://prove2.me/submissions/3448bf06-122c-4e84-bcaa-83dd6e3675f7

import Definitions.Def_RuntimeTransferPacking
import Theorems.Thm_IntMul_HvdH_kronMul_eq

set_option autoImplicit false
namespace RuntimeTransfer

end RuntimeTransfer

open RuntimeTransfer
theorem solution (p r : ℕ) (a b : List ℤ)
    (ha : a.length = r) (hb : b.length = r)
    (hab : ∀ x ∈ a, |x| ≤ 2 ^ p) (hbb : ∀ x ∈ b, |x| ≤ 2 ^ p)
    (hr : 1 ≤ r) (hrp : 2 * r < 2 ^ p)
    (oracle : (ℤ × ℤ) → ℤ × ℕ) (T : (ℤ × ℤ) → ℕ) (E D : ℕ)
    (hcorrect : ∀ q, (oracle q).1 = q.1 * q.2)
    (hcost : ∀ q, (oracle q).2 ≤ T q) :
    ((packingProgram p r a b E D).run oracle).1 = IntMul.HvdH.polyMul a b ∧
      ((packingProgram p r a b E D).run oracle).2 ≤ E + D + T (packedQuery p a b) := by
  simp only [packingProgram, Program.run, hcorrect]
  constructor
  · exact IntMul.HvdH.kronMul_eq p r a b ha hb hab hbb hr hrp
  · simpa only [Nat.add_zero, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      using Nat.add_le_add_left (Nat.add_le_add_right (hcost (packedQuery p a b)) D) E

#print axioms solution
