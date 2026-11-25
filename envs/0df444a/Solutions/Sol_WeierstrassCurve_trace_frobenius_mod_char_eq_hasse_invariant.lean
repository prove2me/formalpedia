-- Prove2me | solution 1 for WeierstrassCurve.trace_frobenius_mod_char_eq_hasse_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-25T01:29:51.372638+00:00
-- url     : https://prove2.me/submissions/56e00b78-fa39-45bb-9a8c-c5a4c8fbe727

import Mathlib
import Definitions.Def_RPLib_S3_SSHasseB

set_option autoImplicit false

open Polynomial

theorem solution
    {F : Type*} [Field F] [Fintype F] (p : ℕ) [Fact p.Prime] [CharP F p] (hp : p ≠ 2)
    {m : ℕ} (hq : Fintype.card F = p ^ m) (W : WeierstrassCurve F) [W.IsElliptic] :
    ((((Fintype.card F : ℤ) + 1 - (Nat.card W.toAffine.Point : ℤ) : ℤ) : F) =
        (W.Ψ₂Sq ^ ((Fintype.card F - 1) / 2)).coeff (Fintype.card F - 1)) ∧
    ((((Fintype.card F : ℤ) + 1 - (Nat.card W.toAffine.Point : ℤ) : ℤ) : F) =
        (W.Ψ₂Sq ^ ((p - 1) / 2)).coeff (p - 1) ^ (∑ i ∈ Finset.range m, p ^ i)) ∧
    ((p : ℤ) ∣ (Fintype.card F : ℤ) + 1 - (Nat.card W.toAffine.Point : ℤ) ↔
        (W.Ψ₂Sq ^ ((p - 1) / 2)).coeff (p - 1) = 0) := by
  classical
  have hF : ringChar F ≠ 2 := by rw [ringChar.eq F p]; exact hp
  have hg : RamanujanPetersson.S3.DWSS.gE W = W.Ψ₂Sq := rfl
  have hodd : Fintype.card F % 2 = 1 := FiniteField.odd_card_of_char_ne_two hF
  have htr : RPLib.EllFq.trace W =
      (Fintype.card F : ℤ) + 1 - (Nat.card W.toAffine.Point : ℤ) := by
    rw [RPLib.EllFq.trace, RPLib.EllFq.numPoints, Nat.card_eq_fintype_card (α := F)]
  have h1 : (((Fintype.card F : ℤ) + 1 - (Nat.card W.toAffine.Point : ℤ) : ℤ) : F) =
      (W.Ψ₂Sq ^ ((Fintype.card F - 1) / 2)).coeff (Fintype.card F - 1) := by
    rw [← htr, RamanujanPetersson.S3.DWSS.trace_cast_eq_coeff hF W, hg]
    congr 2
    omega
  have hM : ∀ k : ℕ, RamanujanPetersson.S3.DWSS.hasseM p k W =
      RamanujanPetersson.S3.DWSS.hasseA p W ^ (∑ i ∈ Finset.range k, p ^ i) := by
    intro k
    induction k with
    | zero => simp [RamanujanPetersson.S3.DWSS.hasseM_zero]
    | succ k ih =>
      rw [RamanujanPetersson.S3.DWSS.hasseM_succ p hp, ih, ← pow_mul, ← pow_succ',
        Finset.sum_range_succ', pow_zero]
      congr 1
      rw [Finset.sum_mul]
      simp only [pow_succ]
  have h2 : (((Fintype.card F : ℤ) + 1 - (Nat.card W.toAffine.Point : ℤ) : ℤ) : F) =
      (W.Ψ₂Sq ^ ((p - 1) / 2)).coeff (p - 1) ^ (∑ i ∈ Finset.range m, p ^ i) := by
    rw [h1, hq]
    exact hM m
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · have h1F := Fintype.one_lt_card (α := F)
      rw [hq, h0, pow_zero] at h1F
      omega
    · exact h0
  have hS : (∑ i ∈ Finset.range m, p ^ i) ≠ 0 := by
    refine (Finset.sum_pos (fun i _ => pow_pos (Fact.out : p.Prime).pos i) ?_).ne'
    exact ⟨0, Finset.mem_range.mpr hm⟩
  refine ⟨h1, h2, ?_⟩
  rw [← CharP.intCast_eq_zero_iff F p, h2, pow_eq_zero_iff hS]

