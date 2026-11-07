-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.adjoin_square_generator_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:31:20.182187+00:00
-- url     : https://prove2.me/submissions/6c4aeaa4-570e-4853-b55b-05b02982cf95

import Definitions.Def_QEC_Coding_ExpanderCodes_FiniteFieldQuadraticSplitting
import Mathlib.GroupTheory.Coset.Card
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Tactic.Linarith
import Definitions.Def_QEC_Coding_ExpanderCodes_FiniteFieldSquareParameters

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes
open IntermediateField
namespace QEC.Coding.ExpanderCodes
theorem _root_.solution {F K : Type*} [Field F] [Field K]
    [Finite K] [Algebra F K] (g : Kˣ) (hg : ∀ x : Kˣ, x ∈ Subgroup.zpowers g) :
    adjoin F ({(g : K) ^ 2} : Set K) = ⊤ := by
  classical
  let S := adjoin F ({(g : K) ^ 2} : Set K)
  let : Fintype S := Fintype.ofFinite S
  have hS : 1 < Nat.card S := Finite.one_lt_card
  have hK : 1 < Nat.card K := Finite.one_lt_card
  have hPow : g ^ (2 * (Nat.card S - 1)) = 1 := by
    let a : S := ⟨(g : K) ^ 2, mem_adjoin_simple_self F ((g : K) ^ 2)⟩
    have ha : a ≠ 0 := by
      intro hZero
      exact pow_ne_zero 2 g.ne_zero (congrArg Subtype.val hZero)
    have h := FiniteField.pow_card_sub_one_eq_one a ha
    have hField := congrArg (fun x : S => (x : K)) h
    change ((g : K) ^ 2) ^ (Fintype.card S - 1) = 1 at hField
    apply Units.ext
    simpa only [Units.val_pow_eq_pow_val, Units.val_one, ← pow_mul,
      Nat.card_eq_fintype_card] using hField
  have hDvd : Nat.card K - 1 ∣ 2 * (Nat.card S - 1) := by
    rw [← Nat.card_units, ← orderOf_eq_card_of_forall_mem_zpowers hg]
    exact orderOf_dvd_of_pow_eq_one hPow
  by_contra hProper
  have hMissing : ∃ x : K, x ∉ S := by
    by_contra hMissing
    push Not at hMissing
    apply hProper
    apply top_unique
    intro x _
    exact hMissing x
  obtain ⟨x, hx⟩ := hMissing
  have hLt : Nat.card S < Nat.card K := Finite.card_subtype_lt hx
  have hAddDvd : Nat.card S ∣ Nat.card K :=
    AddSubgroup.card_addSubgroup_dvd_card S.toSubfield.toSubring.toAddSubgroup
  obtain ⟨k, hk⟩ := hDvd
  have hkPositive : 0 < k := by
    by_contra hkNot
    have hkZero : k = 0 := by omega
    simp only [hkZero, mul_zero] at hk
    omega
  have hkLt : k < 2 := by
    have hBound : 2 * (Nat.card S - 1) < 2 * (Nat.card K - 1) := by omega
    nlinarith
  have hkOne : k = 1 := by omega
  rw [hkOne, mul_one] at hk
  have hAdd : Nat.card S ∣ Nat.card K + 1 := by
    exact ⟨2, by omega⟩
  have hOne : Nat.card S ∣ 1 := by
    simpa using Nat.dvd_sub hAdd hAddDvd
  have := Nat.le_of_dvd (by decide : 0 < 1) hOne
  omega
end QEC.Coding.ExpanderCodes
