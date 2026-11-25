-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.frobFix_root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:42:39.065723+00:00
-- url     : https://prove2.me/submissions/89f4a88c-23d4-4c3d-9c13-4d3850c78475

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_KurDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FrobFixNegOne

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
open Formalism.L2.Th1.CM
variable {R : Type*} [CommRing R] (p : ℕ)
variable {p}
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (hp : p.Prime) {x : R} {n : ℕ} (hn : 0 < n) (hpn : ¬ p ∣ n)
    (hx : x ^ n = 1) : FrobFix p x := by
  have hcop : Nat.Coprime p n := (Nat.Prime.coprime_iff_not_dvd hp).2 hpn
  have htot : p ^ n.totient % n = 1 % n := Nat.ModEq.pow_totient hcop
  refine ⟨n.totient, Nat.totient_pos.2 hn, ?_⟩
  have key : ∀ m, x ^ m = x ^ (m % n) := fun m => by
    conv_lhs => rw [← Nat.mod_add_div m n, pow_add, pow_mul, hx, one_pow, mul_one]
  have hx' : x ^ (p ^ n.totient) = x := by
    rw [key, htot, ← key, pow_one]
  rw [hx', sub_self]
  exact dvd_zero _
end ReciprocityTheory.ChartRestriction.L1
