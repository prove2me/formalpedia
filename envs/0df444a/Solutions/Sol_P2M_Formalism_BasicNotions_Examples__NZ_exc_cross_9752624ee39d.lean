-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_exc_cross_9752624ee39d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:32:23.465083+00:00
-- url     : https://prove2.me/submissions/2a5797f8-cdc0-43ae-ba06-d2b958a611df

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeB
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeC
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_coprime_n_8914bd4d6568
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_exc_of_dvd_c4fb5d0e0daf


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.NZ
open Polynomial Formalism.CyclotomicNorms Formalism.CyclotomicNorms.CycleTypeFiniteOrder
variable {g : ℕ} [hg : Fact g.Prime]
namespace Formalism.BasicNotions.Examples₂.NZ
theorem _root_.solution {p s ℓ : ℕ} (hℓ : ℓ.Prime) (hp : 2 ≤ p) (hs : 1 ≤ s) (hc : Nat.Coprime p s)
    (u w : (Fbar g)ˣ) (hu : orderOf u = g ^ p - 1) (hw : orderOf w = g ^ s - 1) (i j c : ℕ)
    (h : ((u : Fbar g) ^ (g ^ i)) ^ (ℓ ^ c) = ((w : Fbar g) ^ (g ^ j)) ^ (ℓ ^ c)) : Exc g p ℓ := by
  have h' : u ^ (g ^ i * ℓ ^ c) = w ^ (g ^ j * ℓ ^ c) := Units.ext (by
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, pow_mul, pow_mul, h])
  have h1 : u ^ (g ^ i * (ℓ ^ c * (g ^ s - 1))) = 1 := by
    rw [← mul_assoc, pow_mul, h', ← pow_mul, mul_comm, pow_mul, ← hw, pow_orderOf_eq_one, one_pow]
  have h2 : g ^ p - 1 ∣ ℓ ^ c * (g ^ s - 1) :=
    ((coprime_n p (by omega)).pow_right i).dvd_of_dvd_mul_left (hu ▸ orderOf_dvd_of_pow_eq_one h1)
  exact exc_of_dvd hg.out.two_le hℓ (by omega) (by rw [hc]; omega) h2
end Formalism.BasicNotions.Examples₂.NZ
