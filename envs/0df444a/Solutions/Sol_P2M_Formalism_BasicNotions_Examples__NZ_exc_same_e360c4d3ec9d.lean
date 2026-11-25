-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_exc_same_e360c4d3ec9d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:32:24.798865+00:00
-- url     : https://prove2.me/submissions/dc32104b-dbe1-4461-9c44-88a8be79e07f

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeB
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeC
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_dvd_of_pow_eq_7b799bd31cc9
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
variable {d : ℕ} (hd : 1 ≤ d) (u : (Fbar g)ˣ) (hu : orderOf u = g ^ d - 1)
include hd hu
namespace Formalism.BasicNotions.Examples₂.NZ
theorem _root_.solution {ℓ : ℕ} (hℓ : ℓ.Prime) {i j c : ℕ} (hi : i < d) (hj : j < d) (hij : i ≠ j)
    (h : ((u : Fbar g) ^ (g ^ i)) ^ (ℓ ^ c) = ((u : Fbar g) ^ (g ^ j)) ^ (ℓ ^ c)) : Exc g d ℓ := by
  have key : ∀ {i j : ℕ}, i < j → j < d → u ^ (g ^ i * ℓ ^ c) = u ^ (g ^ j * ℓ ^ c) → Exc g d ℓ := by
    intro i j hij hj h
    refine exc_of_dvd (e := j - i) hg.out.two_le hℓ hd ?_ (dvd_of_pow_eq hd u hu hij.le h)
    obtain ⟨t, ht⟩ := Nat.gcd_dvd_left d (j - i)
    have h1 : Nat.gcd d (j - i) ≤ j - i := Nat.gcd_le_right _ (by omega)
    have h0 : 0 < Nat.gcd d (j - i) := Nat.gcd_pos_of_pos_left _ hd
    have ht2 : 2 ≤ t := by
      by_contra hlt
      interval_cases t
      · omega
      · omega
    calc 2 * Nat.gcd d (j - i) = Nat.gcd d (j - i) * 2 := mul_comm _ _
      _ ≤ Nat.gcd d (j - i) * t := Nat.mul_le_mul_left _ ht2
      _ = d := ht.symm
  have h' : u ^ (g ^ i * ℓ ^ c) = u ^ (g ^ j * ℓ ^ c) := Units.ext (by
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, pow_mul, pow_mul, h])
  rcases lt_or_gt_of_ne hij with h1 | h1
  · exact key h1 hj h'
  · exact key h1 hi h'.symm
end Formalism.BasicNotions.Examples₂.NZ
