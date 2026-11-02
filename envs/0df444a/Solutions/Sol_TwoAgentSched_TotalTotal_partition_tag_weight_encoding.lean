-- Prove2me | solution 1 for TwoAgentSched.TotalTotal.partition_tag_weight_encoding
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T20:11:45.64871+00:00
-- url     : https://prove2.me/submissions/be71cd49-6203-4a67-9bb7-aa39ccb74fd6

import Mathlib
import Definitions.Def_ProjSchedTW_Complexity_Encoding

set_option autoImplicit false
open ProjSchedTW.Complexity

namespace TwoAgentSched.TotalTotal.BinaryShift

/-- Multiplication by a power of two prepends zero bits to the canonical
    little-endian binary representation of a positive natural number. -/
theorem bits_shift (n r : ℕ) (hn : 0 < n) :
    Nat.bits (2 ^ r * n) = List.replicate r false ++ Nat.bits n := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hne : 2 ^ r * n ≠ 0 := by positivity
    have heq : 2 ^ (r + 1) * n = 2 * (2 ^ r * n) := by rw [pow_succ]; ring
    rw [heq, Nat.bit0_bits _ hne, ih]
    simp [List.replicate_succ]

/-- Zero-padding the encoded positive weight implements a binary shift. -/
theorem encode_shift (n r : ℕ) (hn : 0 < n) :
    encNat (2 ^ r * n) = List.replicate r BSym.zero ++ encNat n := by
  simp [encNat, bits_shift n r hn, List.map_append, List.map_replicate, List.append_assoc]


/-- The number with a low marker bit and a separately shifted positive high
    block is encoded by emitting zero runs and one marker. -/
theorem encode_shifted_tag (m r s : ℕ) (hm : 0 < m) :
    encNat (2 ^ r * (2 * (2 ^ s * m) + 1)) =
      List.replicate r BSym.zero ++ BSym.one ::
        (List.replicate s BSym.zero ++ encNat m) := by
  have hp : 0 < 2 * (2 ^ s * m) + 1 := by omega
  rw [encode_shift _ r hp]
  have hbit : encNat (2 * (2 ^ s * m) + 1) = BSym.one :: encNat (2 ^ s * m) := by
    simp [encNat, Nat.bit1_bits]
  rw [hbit, encode_shift m s hm]


end TwoAgentSched.TotalTotal.BinaryShift

namespace TwoAgentSched.TotalTotal.BinaryShift

/-- Inserting an original weight into the high block of the base-four gadget
    is exactly a low marker followed by a shifted copy of that weight. -/
theorem gadget_power_factor (i d m : ℕ) :
    2 * (4 ^ (i + d + 1) * m + 4 ^ i) =
      2 ^ (2 * i + 1) * (2 * (2 ^ (2 * d + 1) * m) + 1) := by
  have hfour (k : ℕ) : 4 ^ k = 2 ^ (2 * k) := by
    rw [pow_mul]
    norm_num
  rw [hfour (i + d + 1), hfour i]
  have he : 2 * (i + d + 1) = 2 * i + 1 + (2 * d + 1) := by omega
  rw [he]
  simp only [pow_add, pow_one]
  ring

end TwoAgentSched.TotalTotal.BinaryShift

open TwoAgentSched.TotalTotal.BinaryShift

/-- The exact canonical little-endian code of the high-weight member of a
    positive base-four gadget pair consists of two zero runs, one marker,
    and the original input code. -/
theorem solution (i d m : ℕ) (hm : 0 < m) :
    encNat (2 * (4 ^ (i + d + 1) * m + 4 ^ i)) =
      List.replicate (2 * i + 1) BSym.zero ++ BSym.one ::
        (List.replicate (2 * d + 1) BSym.zero ++ encNat m) := by
  rw [gadget_power_factor]
  exact encode_shifted_tag m (2 * i + 1) (2 * d + 1) hm

