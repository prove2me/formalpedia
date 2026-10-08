-- Prove2me | solution 1 for SemialgebraicSDP.Psatz.monomial_vector_card
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T06:19:49.192176+00:00
-- url     : https://prove2.me/submissions/1f564e6f-ae19-47fa-a848-4c1fd6d02221

import Mathlib
import Definitions.Def_SemialgebraicSDP_Psatz_Gram

open SemialgebraicSDP.Psatz MvPolynomial

private def slackEquiv (n d : ℕ) :
    Mon n d ≃ {a : Option (Fin n) → ℕ // ∑ i, a i = d} where
  toFun a := ⟨fun i => match i with
    | none => d - ∑ j, (a.1 j : ℕ)
    | some j => (a.1 j : ℕ), by
      simp only [Fintype.sum_option]
      exact Nat.sub_add_cancel a.2⟩
  invFun a := ⟨fun j => ⟨a.1 (some j), by
    have he := a.2
    rw [Fintype.sum_option] at he
    have hb := Finset.single_le_sum (fun k _ => Nat.zero_le (a.1 (some k)))
      (Finset.mem_univ j)
    omega⟩, by
      have he := a.2
      rw [Fintype.sum_option] at he
      dsimp
      omega⟩
  left_inv a := by
    apply Subtype.ext
    funext j
    rfl
  right_inv a := by
    apply Subtype.ext
    funext i
    cases i with
    | none =>
      have he := a.2
      rw [Fintype.sum_option] at he
      dsimp
      omega
    | some j => rfl

theorem SemialgebraicSDP.Psatz.monomial_vector_card (n d : ℕ) :
    Fintype.card (Mon n d) = (n + d).choose d := by
  classical
  let e := (slackEquiv n d).trans (Sym.equivNatSumOfFintype (Option (Fin n)) d).symm
  rw [Fintype.card_congr e, Sym.card_sym_eq_choose]
  simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem solution (n d : ℕ) :
    Fintype.card (Mon n d) = (n + d).choose d :=
  SemialgebraicSDP.Psatz.monomial_vector_card n d

#print axioms solution
