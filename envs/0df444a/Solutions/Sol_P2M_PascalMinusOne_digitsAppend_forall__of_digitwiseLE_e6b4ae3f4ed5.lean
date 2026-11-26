-- Prove2me | solution 1 for P2M_PascalMinusOne_digitsAppend_forall__of_digitwiseLE_e6b4ae3f4ed5
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:22:28.963845+00:00
-- url     : https://prove2.me/submissions/cbeec93e-d5e0-493e-a989-b0ef0fbddea5

import Definitions.Def_PascalMinusOne_Basic
import Definitions.Def_PascalMinusOne_Digits
import Definitions.Def_PascalMinusOne_Kummer
import Definitions.Def_PascalMinusOne_SignedTokens
import Mathlib.Data.Nat.Digits.Div
import Mathlib.Data.List.GetD
import Definitions.Def_PascalMinusOne_MinusOne
import Theorems.Thm_PascalMinusOne_digitAt_ofDigits_eq_getD

set_option autoImplicit true
open PascalMinusOne
namespace PascalMinusOne
theorem _root_.solution {p k N : ℕ}
    (hp : 2 ≤ p) (hkn : k ≤ N) (hdigit : DigitwiseLE p k N) :
    List.Forall₂ (· ≤ ·)
      (Nat.digitsAppend p (Nat.digits p N).length k)
      (Nat.digits p N) := by
  have hp1 : 1 < p := by omega
  have hkpow : k < p ^ (Nat.digits p N).length :=
    lt_of_le_of_lt hkn
      (Nat.lt_base_pow_length_digits (b := p) (m := N) hp1)
  have hlen :
      (Nat.digitsAppend p (Nat.digits p N).length k).length =
        (Nat.digits p N).length :=
    Nat.length_digitsAppend hp1 _ hkpow
  have hS :
      ∀ s ∈ Nat.digitsAppend p (Nat.digits p N).length k, s < p :=
    fun s hs => Nat.lt_of_mem_digitsAppend hp1 _ s hs
  have hD : ∀ d ∈ Nat.digits p N, d < p :=
    fun d hd => Nat.digits_lt_base hp1 hd
  have hSval :
      Nat.ofDigits p (Nat.digitsAppend p (Nat.digits p N).length k) = k := by
    rw [Nat.digitsAppend, Nat.ofDigits_append_replicate_zero, Nat.ofDigits_digits]
  have hDval : Nat.ofDigits p (Nat.digits p N) = N :=
    Nat.ofDigits_digits p N
  refine List.forall₂_of_length_eq_of_get hlen ?_
  intro i hiS hiD
  have hgetD :
      (Nat.digitsAppend p (Nat.digits p N).length k).getD i 0 ≤
        (Nat.digits p N).getD i 0 := by
    rw [← digitAt_ofDigits_eq_getD hp _ hS, hSval,
      ← digitAt_ofDigits_eq_getD hp _ hD, hDval]
    exact hdigit i
  rw [List.getD_eq_getElem _ _ hiS, List.getD_eq_getElem _ _ hiD] at hgetD
  exact hgetD
end PascalMinusOne
