-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Bridge50.P05.primitiveCyclic
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T12:57:14.43141+00:00
-- url     : https://prove2.me/submissions/ce9eebae-a9c4-4502-b7f5-16d17098c32e

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P05

open QAlgorithms.Papers.Independent.Bridge50.P05
open QAlgorithms.Papers.Independent.Gap48.P36 (WeylLabel)

theorem s110_pc_dvd {d : ℕ} [NeZero d] (x : ZMod d) (m : ℕ) (h : m • x = 0) : d ∣ m * x.val := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  rw [ZMod.natCast_zmod_val, ← nsmul_eq_mul]
  exact h

theorem s110_pc_order {d : ℕ} [NeZero d] (z : WeylLabel d)
    (hg : Nat.gcd (Nat.gcd z.1.val z.2.val) d = 1) : addOrderOf z = d := by
  apply Nat.dvd_antisymm
  · apply addOrderOf_dvd_of_nsmul_eq_zero
    ext <;> simp
  · have h0 := addOrderOf_nsmul_eq_zero z
    set m := addOrderOf z
    have h1 : d ∣ m * z.1.val := s110_pc_dvd _ m (by simpa using congrArg Prod.fst h0)
    have h2 : d ∣ m * z.2.val := s110_pc_dvd _ m (by simpa using congrArg Prod.snd h0)
    have h3 : d ∣ m * Nat.gcd z.1.val z.2.val := by
      rw [← Nat.gcd_mul_left]; exact Nat.dvd_gcd h1 h2
    have hc : Nat.Coprime d (Nat.gcd z.1.val z.2.val) := by
      rw [Nat.coprime_comm]; exact hg
    exact hc.dvd_of_dvd_mul_right h3

theorem s110_pc_ncard {d : ℕ} [NeZero d] (z : WeylLabel d)
    (hg : Nat.gcd (Nat.gcd z.1.val z.2.val) d = 1) :
    (AddSubgroup.zmultiples z : Set (WeylLabel d)).ncard = d := by
  rw [← Nat.card_coe_set_eq]
  simp only [SetLike.coe_sort_coe]
  rw [Nat.card_zmultiples, s110_pc_order z hg]

theorem solution {d : ℕ} [NeZero d] (z : WeylLabel d) :
    Degenerate (AddSubgroup.zmultiples z : Set (WeylLabel d)) ∧
    (Nat.gcd (Nat.gcd z.1.val z.2.val) d = 1 →
      (AddSubgroup.zmultiples z : Set (WeylLabel d)).ncard = d) ∧
    (Nat.Prime d → z ≠ 0 → (AddSubgroup.zmultiples z : Set (WeylLabel d)).ncard = d) := by
  refine ⟨?_, s110_pc_ncard z, ?_⟩
  · rintro u ⟨a, rfl⟩ v ⟨b, rfl⟩
    show (a • z).1 * (b • z).2 - (a • z).2 * (b • z).1 = 0
    rw [Prod.smul_fst, Prod.smul_snd, Prod.smul_fst, Prod.smul_snd]
    simp only [zsmul_eq_mul]
    ring
  · intro hp hz
    apply s110_pc_ncard z
    rcases (Nat.coprime_or_dvd_of_prime hp (Nat.gcd z.1.val z.2.val)) with h | h
    · rw [Nat.gcd_comm]; exact h
    · exfalso; apply hz
      have h1 : d ∣ z.1.val := h.trans (Nat.gcd_dvd_left _ _)
      have h2 : d ∣ z.2.val := h.trans (Nat.gcd_dvd_right _ _)
      have e1 : z.1.val = 0 := Nat.eq_zero_of_dvd_of_lt h1 (ZMod.val_lt _)
      have e2 : z.2.val = 0 := Nat.eq_zero_of_dvd_of_lt h2 (ZMod.val_lt _)
      ext
      · exact (ZMod.val_eq_zero _).1 e1
      · exact (ZMod.val_eq_zero _).1 e2
