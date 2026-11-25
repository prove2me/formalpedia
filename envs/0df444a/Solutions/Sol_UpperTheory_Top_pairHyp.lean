-- Prove2me | solution 1 for UpperTheory.Top.pairHyp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:46:54.24046+00:00
-- url     : https://prove2.me/submissions/3d17b6fc-2bc0-41f2-8fb0-f6340856b805

import Definitions.Def_Development_AutomorphicArithmetic_CharacterBoxes_TwistForm
import Definitions.Def_Development_AutomorphicArithmetic_CharacterBoxes_PairHyp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Formalism.HC Formalism.FrobeniusOrbits UpperTheory.Top
private theorem jac_neg_of_dvd {p d : ℕ} (h : p ∣ d + 1) : jacobiSym (-(d : ℤ)) p = 1 := by
  have h1 : (-(d : ℤ)) ≡ 1 [ZMOD (p : ℤ)] := by
    apply Int.modEq_iff_dvd.2
    have h2 := Int.natCast_dvd_natCast.2 h
    push_cast at h2
    have h3 : (1 : ℤ) - -(d : ℤ) = (d : ℤ) + 1 := by ring
    rw [h3]
    exact h2
  rw [jacobiSym.mod_left' h1, jacobiSym.one_left]
private theorem jac_neg_recip {n a : ℕ} (hn : n % 4 = 3) (ha : Odd a) :
    jacobiSym (-(n : ℤ)) a = jacobiSym (a : ℤ) n := by
  have hno : Odd n := Nat.odd_iff.2 (by omega)
  rw [jacobiSym.neg _ ha]
  rcases Nat.odd_mod_four_iff.1 (Nat.odd_iff.1 ha) with h | h
  · rw [ZMod.χ₄_nat_one_mod_four h, one_mul, jacobiSym.quadratic_reciprocity_one_mod_four h hno]
  · rw [ZMod.χ₄_nat_three_mod_four h, jacobiSym.quadratic_reciprocity_three_mod_four h hn]
    ring
end

set_option autoImplicit false
open Formalism.HC Formalism.FrobeniusOrbits UpperTheory.Top
namespace UpperTheory.Top
theorem _root_.solution :
    ∀ (eps Y : ℝ) (q d : ℕ), WinPair eps Y q d → HostHyp q d ∧
      (∀ p : ℕ, p.Prime → p ≠ 2 → (p : ℝ) ≤ Y ^ (eps / 5) → jacobiSym (-(d : ℤ)) p = 1) ∧
      (∀ a : ℕ, Odd a → jacobiSym (-(q : ℤ)) a = jacobiSym (a : ℤ) q ∧ jacobiSym (-(d : ℤ)) a = jacobiSym (a : ℤ) d) := by
  intro eps Y q d hw
  have hq4 : q % 4 = 3 := by have := hw.q_mod; omega
  have hd4 : d % 4 = 3 := by have := hw.d_mod; omega
  refine ⟨⟨hw.q_prime, hw.d_prime, hw.q_mod, hw.d_mod, jac_neg_of_dvd hw.d_q⟩, ?_, ?_⟩
  · intro p hp hp2 hpY
    exact jac_neg_of_dvd (hw.d_small p hp hp2 hpY)
  · intro a ha
    exact ⟨jac_neg_recip hq4 ha, jac_neg_recip hd4 ha⟩
end UpperTheory.Top
