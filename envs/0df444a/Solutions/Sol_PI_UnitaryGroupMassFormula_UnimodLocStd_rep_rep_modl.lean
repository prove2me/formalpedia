-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.rep_rep_modl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:51:02.946122+00:00
-- url     : https://prove2.me/submissions/5e632b3e-b400-4b69-ae47-119310cb51b0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepRepModl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnimodLocStd
open Polynomial
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
theorem _root_.solution {l : ℕ} (hl : l.Prime) (a : ℕ) (b c : ℤ) (d : ℕ) (hOK : 4 * (a : ℤ) * c = b ^ 2 + d)
    (hld : ¬ (l : ℤ) ∣ d) (N S Q0 : ℤ) (hN : ¬ (l : ℤ) ∣ N) (hS : ¬ (l : ℤ) ∣ S) (hQ : ¬ (l : ℤ) ∣ Q0) :
    ∃ s t : ℤ, (l : ℤ) ∣ (s ^ 2 + b * s * t + a * c * t ^ 2) * N - Q0 * S := by
  have normForm_surj_zmod_lemma {l : ℕ} [Fact l.Prime] (A B : ZMod l) (D : ZMod l)
      (hOK : 4 * A = B ^ 2 + D) (hD : D ≠ 0) (v : ZMod l) (hv : v ≠ 0) :
      ∃ s t : ZMod l, s ^ 2 + B * s * t + A * t ^ 2 = v := by
    have hl : l.Prime := Fact.out
    rcases hl.eq_two_or_odd with rfl | hodd
    · refine ⟨1, 0, ?_⟩
      have h1 : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by
        intro x hx; fin_cases x
        · exact absurd rfl hx
        · rfl
      rw [h1 v hv]; ring
    · have hl2 : l ≠ 2 := by omega
      have h2 : (2 : ZMod l) ≠ 0 := Ring.two_ne_zero (by rw [ZMod.ringChar_zmod_n]; exact hl2)
      have hcard : Fintype.card (ZMod l) % 2 = 1 := by rw [ZMod.card]; exact hodd
      open Polynomial in
      have hf : ((X : (ZMod l)[X]) ^ 2).degree = 2 := by
        rw [degree_X_pow]; rfl
      open Polynomial in
      have hdeg : (C D * X ^ 2 : (ZMod l)[X]).degree = 2 := by
        rw [degree_C_mul_X_pow 2 hD]; rfl
      open Polynomial in
      have hg : (C D * X ^ 2 - C (4 * v) : (ZMod l)[X]).degree = 2 := by
        rw [degree_sub_C (by rw [hdeg]; decide), hdeg]
      obtain ⟨x, y, hxy⟩ := FiniteField.exists_root_sum_quadratic hf hg hcard
      simp only [Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_C] at hxy
      set i : ZMod l := (2 : ZMod l)⁻¹ with hi_def
      have hi : 2 * i = 1 := mul_inv_cancel₀ h2
      refine ⟨(x - B * y) * i, y, ?_⟩
      have h4 : (4 : ZMod l) ≠ 0 := by
        have : (4 : ZMod l) = 2 * 2 := by norm_num
        rw [this]; exact mul_ne_zero h2 h2
      apply mul_left_cancel₀ h4
      linear_combination hxy + y ^ 2 * hOK + ((2 * i + 1) * (x - B * y) ^ 2 + 2 * B * y * (x - B * y)) * hi
  have := Fact.mk hl
  have : NeZero l := ⟨hl.ne_zero⟩
  have nz : ∀ z : ℤ, ¬ (l : ℤ) ∣ z → (z : ZMod l) ≠ 0 := fun z hz h =>
    hz ((ZMod.intCast_zmod_eq_zero_iff_dvd z l).mp h)
  have hOK' : 4 * (((a : ℤ) : ZMod l) * (c : ZMod l)) = (b : ZMod l) ^ 2 + ((d : ℤ) : ZMod l) := by
    have := congrArg (Int.cast : ℤ → ZMod l) hOK
    push_cast at this ⊢
    linear_combination this
  have hN' := nz N hN
  obtain ⟨s, t, hst⟩ := normForm_surj_zmod_lemma (((a : ℤ) : ZMod l) * (c : ZMod l)) (b : ZMod l)
    ((d : ℤ) : ZMod l) hOK' (nz _ hld) ((Q0 : ZMod l) * (S : ZMod l) * (N : ZMod l)⁻¹)
    (mul_ne_zero (mul_ne_zero (nz _ hQ) (nz _ hS)) (inv_ne_zero hN'))
  refine ⟨(s.val : ℤ), (t.val : ℤ), ?_⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hs : ((s.val : ℤ) : ZMod l) = s := by rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have ht : ((t.val : ℤ) : ZMod l) = t := by rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_add, Int.cast_pow, hs, ht]
  have hst' : s ^ 2 + (b : ZMod l) * s * t + ((a : ℤ) : ZMod l) * (c : ZMod l) * t ^ 2
      = (Q0 : ZMod l) * (S : ZMod l) * (N : ZMod l)⁻¹ := hst
  rw [hst', mul_assoc, inv_mul_cancel₀ hN', mul_one, sub_self]
end PI.UnitaryGroupMassFormula.UnimodLocStd
