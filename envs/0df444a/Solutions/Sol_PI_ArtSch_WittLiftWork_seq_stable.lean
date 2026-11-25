-- Prove2me | solution 1 for PI.ArtSch.WittLiftWork.seq_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:38:55.193932+00:00
-- url     : https://prove2.me/submissions/fb098c79-1305-400b-a970-680cdddfacef

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ArtSch
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittCoefficients_CoeffEqOfSubMem
import Theorems.Thm_PI_ArtSch_WittLiftWork_I_anti
import Theorems.Thm_PI_ArtSch_WittLiftWork_seq_succ_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.ArtSch PI.ArtSch.WittLiftWork
open WittVector
variable {p : ℕ} [hp : Fact p.Prime] {k : Type} [CommRing k]
variable [CharP k p]
variable (hAS : ∀ a : k, ∃ y : k, y ^ p - y = a)
include hAS
namespace PI.ArtSch.WittLiftWork
theorem _root_.solution (x : WittVector p k) (n : ℕ) :
    ∀ m, n ≤ m → (seq hAS x m).1 - (seq hAS x n).1 ∈ I n := by
  intro m hm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  clear hm
  induction d with
  | zero =>
    simp only [Nat.add_zero, sub_self]
    exact Ideal.zero_mem _
  | succ d ih =>
    have h1 := I_anti (Nat.le_add_right n d)
      (seq_succ_sub hAS x (n + d))
    have e : (seq hAS x (n + d + 1)).1 - (seq hAS x n).1 =
        ((seq hAS x (n + d + 1)).1 - (seq hAS x (n + d)).1) +
          ((seq hAS x (n + d)).1 - (seq hAS x n).1) := by abel
    rw [show n + (d + 1) = n + d + 1 from (Nat.add_assoc n d 1).symm, e]
    exact Ideal.add_mem _ h1 ih
end PI.ArtSch.WittLiftWork
