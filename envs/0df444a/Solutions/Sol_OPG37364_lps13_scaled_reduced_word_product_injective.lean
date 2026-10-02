-- Prove2me | solution 1 for OPG37364.lps13_scaled_reduced_word_product_injective
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-09-12T04:35:13.390688+00:00
-- url     : https://prove2.me/submissions/7b84cd6f-3270-4fb1-9da4-7bd1c11686bb

import Theorems.Thm_OPG37364_lps13_reduced_word_not_all_coords_dvd13
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Induction

set_option autoImplicit false

namespace OPG37364
namespace ScaledWordInjectivity

-- These two structural identities are reused from Stage 7, LPS13Graph.lean.
theorem conj_involutive : Function.Involutive lps13ConjIndex := by
  change ∀ a, lps13ConjIndex (lps13ConjIndex a) = a
  decide

theorem quaternion_conj (a : Fin 14) :
    lps13Quaternion (lps13ConjIndex a) = star (lps13Quaternion a) := by
  fin_cases a <;> rfl

theorem generator_mul_conj (a : Fin 14) :
    lps13Quaternion a * lps13Quaternion (lps13ConjIndex a) =
      (13 : ℤ) • (1 : Quaternion ℤ) := by
  rw [quaternion_conj, Quaternion.self_mul_star, lps13Quaternion_norm]
  rfl

-- The norm induction is reused from Stage 11, LPS13WordPrimitivity.lean.
theorem word_norm (w : List (Fin 14)) :
    Quaternion.normSq (lps13WordProduct w) = (13 : ℤ) ^ w.length := by
  induction w with
  | nil => simp [lps13WordProduct]
  | cons a w ih =>
    simpa [lps13WordProduct, map_mul, lps13Quaternion_norm, pow_succ, mul_comm] using
      congrArg (fun z : ℤ => 13 * z) ih

-- This interface to List.IsChain is reused from Stage 12, LPS13CycleWords.lean.
theorem reduced_iff_chain (w : List (Fin 14)) :
    lps13WordReduced w ↔ w.IsChain (fun a b => b ≠ lps13ConjIndex a) := by
  induction w with
  | nil => simp [lps13WordReduced]
  | cons a w ih =>
    cases w with
    | nil => simp [lps13WordReduced]
    | cons b w =>
      simpa only [lps13WordReduced, List.isChain_cons_cons] using and_congr Iff.rfl ih

theorem product_append (u v : List (Fin 14)) :
    lps13WordProduct (u ++ v) = lps13WordProduct u * lps13WordProduct v := by
  simp [lps13WordProduct]

theorem product_snoc (u : List (Fin 14)) (a : Fin 14) :
    lps13WordProduct (u ++ [a]) = lps13WordProduct u * lps13Quaternion a := by
  simp [lps13WordProduct]

theorem scalar_cancel {c : ℤ} (hc : c ≠ 0) {x y : Quaternion ℤ}
    (h : c • x = c • y) : x = y := by
  apply Quaternion.ext
  · exact mul_left_cancel₀ hc (congrArg (fun z : Quaternion ℤ => z.re) h)
  · exact mul_left_cancel₀ hc (congrArg (fun z : Quaternion ℤ => z.imI) h)
  · exact mul_left_cancel₀ hc (congrArg (fun z : Quaternion ℤ => z.imJ) h)
  · exact mul_left_cancel₀ hc (congrArg (fun z : Quaternion ℤ => z.imK) h)

theorem primitive_not_thirteen_smul (w : List (Fin 14)) (hw : lps13WordReduced w)
    (x : Quaternion ℤ) : lps13WordProduct w ≠ (13 : ℤ) • x := by
  intro h
  apply lps13_reduced_word_not_all_coords_dvd13 w hw
  rw [h]
  exact ⟨⟨x.re, rfl⟩, ⟨x.imI, rfl⟩, ⟨x.imJ, rfl⟩, ⟨x.imK, rfl⟩⟩

theorem product_snoc_mul_conj (u : List (Fin 14)) (a : Fin 14) :
    lps13WordProduct (u ++ [a]) * lps13Quaternion (lps13ConjIndex a) =
      (13 : ℤ) • lps13WordProduct u := by
  rw [product_snoc, mul_assoc, generator_mul_conj, mul_smul_comm, mul_one]

theorem reduced_prefix (u : List (Fin 14)) (a : Fin 14)
    (h : lps13WordReduced (u ++ [a])) : lps13WordReduced u :=
  (reduced_iff_chain u).2 ((reduced_iff_chain _).1 h).left_of_append

theorem reduced_extend (v : List (Fin 14)) (a b : Fin 14)
    (hv : lps13WordReduced (v ++ [b])) (hab : a ≠ b) :
    lps13WordReduced ((v ++ [b]) ++ [lps13ConjIndex a]) := by
  apply (reduced_iff_chain _).2
  apply ((reduced_iff_chain _).1 hv).append (by simp)
  simpa using fun (h : lps13ConjIndex a = lps13ConjIndex b) =>
    hab (conj_involutive.injective h)

theorem product_injective_of_length (u v : List (Fin 14))
    (hu : lps13WordReduced u) (hv : lps13WordReduced v)
    (hlen : u.length = v.length) (hprod : lps13WordProduct u = lps13WordProduct v) :
    u = v := by
  induction u using List.reverseRecOn generalizing v with
  | nil => exact (List.length_eq_zero_iff.mp hlen.symm).symm
  | append_singleton u a ih =>
    have hvne : v ≠ [] := by intro h; simp [h] at hlen
    obtain ⟨v, b, rfl⟩ : ∃ t b, v = t ++ [b] :=
      ⟨v.dropLast, v.getLast hvne, (List.dropLast_concat_getLast hvne).symm⟩
    have hab : a = b := by
      by_contra hab
      apply primitive_not_thirteen_smul _ (reduced_extend v a b hv hab) (lps13WordProduct u)
      rw [product_snoc, ← hprod, product_snoc_mul_conj]
    subst b
    have hpref : lps13WordProduct u = lps13WordProduct v := by
      apply scalar_cancel (by norm_num : (13 : ℤ) ≠ 0)
      simpa only [product_snoc_mul_conj] using
        congrArg (fun x => x * lps13Quaternion (lps13ConjIndex a)) hprod
    have huv := ih v (reduced_prefix u a hu) (reduced_prefix v a hv)
      (by simpa using hlen) hpref
    rw [huv]

theorem exponent_not_lt (r s : ℕ) (u v : List (Fin 14))
    (hu : lps13WordReduced u)
    (h : (13 : ℤ)^r • lps13WordProduct u = (13 : ℤ)^s • lps13WordProduct v) :
    ¬ r < s := by
  intro hrs
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hrs)
  have hs : s = r + (d + 1) := by omega
  have he : lps13WordProduct u = (13 : ℤ) • ((13 : ℤ)^d • lps13WordProduct v) := by
    apply scalar_cancel (pow_ne_zero r (by norm_num : (13 : ℤ) ≠ 0))
    simpa only [hs, pow_add, pow_succ', mul_smul] using h
  exact primitive_not_thirteen_smul u hu _ he

end ScaledWordInjectivity

end OPG37364

open OPG37364

/-- Literal integral quaternion equality determines both the power of 13 and the reduced word. -/
theorem solution
    (r s : ℕ) (u v : List (Fin 14))
    (hu : lps13WordReduced u) (hv : lps13WordReduced v)
    (h : (13 : ℤ)^r • lps13WordProduct u = (13 : ℤ)^s • lps13WordProduct v) :
    r = s ∧ u = v := by
  have hrs : r = s := by
    have h₁ := ScaledWordInjectivity.exponent_not_lt r s u v hu h
    have h₂ := ScaledWordInjectivity.exponent_not_lt s r v u hv h.symm
    omega
  subst s
  have hp := ScaledWordInjectivity.scalar_cancel
    (pow_ne_zero r (by norm_num : (13 : ℤ) ≠ 0)) h
  have hn := congrArg Quaternion.normSq hp
  rw [ScaledWordInjectivity.word_norm, ScaledWordInjectivity.word_norm] at hn
  have hl := (pow_right_strictMono₀ (by norm_num : (1 : ℤ) < 13)).injective hn
  exact ⟨rfl, ScaledWordInjectivity.product_injective_of_length u v hu hv hl hp⟩

