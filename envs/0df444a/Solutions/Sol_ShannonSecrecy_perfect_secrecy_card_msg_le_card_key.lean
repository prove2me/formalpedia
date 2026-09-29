-- Prove2me | solution 1 for ShannonSecrecy.perfect_secrecy_card_msg_le_card_key
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T22:24:51.613474+00:00
-- url     : https://prove2.me/submissions/f95a6de1-1384-418c-bcc4-ecaa94ef25bc

import Mathlib
import Definitions.Def_shannon_secrecy_system

set_option autoImplicit false

open ShannonSecrecy
theorem solution
    {M K E : Type*} [Fintype M] [Fintype K] [Fintype E] [DecidableEq E]
    (C : Cipher M K E) (h : PerfectSecrecy C) :
    Fintype.card M ≤ Fintype.card K := by
  classical
  rcases isEmpty_or_nonempty M with hM | hM
  · simp [Fintype.card_eq_zero]
  have hcard : 0 < Fintype.card M := Fintype.card_pos
  set p : M → ℝ := fun _ => (Fintype.card M : ℝ)⁻¹ with hpdef
  have hpos : 0 < (Fintype.card M : ℝ)⁻¹ := by positivity
  have hp : IsPMF p := by
    refine ⟨fun _ => hpos.le, ?_⟩
    simp only [hpdef, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  obtain ⟨k0, hk0⟩ : ∃ k, 0 < C.keyProb k := by
    by_contra hcon
    push Not at hcon
    have : ∑ k, C.keyProb k ≤ 0 := Finset.sum_nonpos (fun k _ => hcon k)
    linarith [C.keyProb_sum]
  obtain ⟨m0⟩ := hM
  set e := C.encipher k0 m0 with he
  have hnn : ∀ m k, 0 ≤ (if C.encipher k m = e then p m * C.keyProb k else 0) := by
    intro m k
    split_ifs
    · exact mul_nonneg hpos.le (C.keyProb_nonneg _)
    · exact le_rfl
  have hce : cryptoProb C p e ≠ 0 := by
    apply ne_of_gt
    unfold cryptoProb
    calc (0 : ℝ) < p m0 * C.keyProb k0 := mul_pos hpos hk0
      _ = (if C.encipher k0 m0 = e then p m0 * C.keyProb k0 else 0) := by rw [if_pos he.symm]
      _ ≤ ∑ k, (if C.encipher k m0 = e then p m0 * C.keyProb k else 0) :=
          Finset.single_le_sum (fun k _ => hnn m0 k) (Finset.mem_univ k0)
      _ ≤ ∑ m, ∑ k, (if C.encipher k m = e then p m * C.keyProb k else 0) :=
          Finset.single_le_sum (f := fun m => ∑ k, (if C.encipher k m = e then p m * C.keyProb k else 0))
            (fun m _ => Finset.sum_nonneg fun k _ => hnn m k) (Finset.mem_univ m0)
  have hex : ∀ m, ∃ k, C.encipher k m = e := by
    intro m
    by_contra hno
    push Not at hno
    have hpost := h p hp e hce m
    unfold postProb at hpost
    simp only [hno, if_false, Finset.sum_const_zero, zero_div] at hpost
    have : p m = (Fintype.card M : ℝ)⁻¹ := rfl
    linarith
  choose f hf using hex
  have finj : Function.Injective f := by
    intro m1 m2 h12
    apply C.encipher_injective (f m1)
    rw [hf m1, h12, hf m2]
  exact Fintype.card_le_of_injective f finj
