-- Prove2me | solution 1 for SZ.Slice.pick_adm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:26:55.111583+00:00
-- url     : https://prove2.me/submissions/25dac9a8-50f4-4e43-8555-44038bcfc1ca

import Definitions.Def_SZ_Defs
import Definitions.Def_SZ_DigitParity
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Definitions.Def_SZ_Slice
import Theorems.Thm_P2M_SZ_Slice_U_def__de67dd39ecba
import Theorems.Thm_P2M_SZ_Slice_gap__61b112f6735f
import Theorems.Thm_SZ_Slice_p_pos
import Theorems.Thm_SZ_Slice_e_pos
import Theorems.Thm_SZ_Slice_bsel_le
import Theorems.Thm_SZ_Slice_bsel_dvd
import Theorems.Thm_SZ_Slice_asel_dvd
import Theorems.Thm_SZ_Slice_bsel_nonneg
import Theorems.Thm_SZ_Slice_bsel_mul_le
import Theorems.Thm_SZ_Slice_lt_bsel_add
import Theorems.Thm_SZ_Slice_asel_eq_zero
import Theorems.Thm_SZ_Slice_asel_lt
import Theorems.Thm_SZ_Slice_le_asel

set_option autoImplicit false
open SZ
open Filter Topology
open SZ.Slice
variable (S : Slice)
namespace SZ.Slice
theorem _root_.solution {w : ℝ} (h0 : 0 ≤ w) (h1 : w ≤ (S.m : ℝ) * S.U) :
    S.PDigit (S.pick w).1 ∧ S.PDigit (S.pick w).2 ∧
      0 ≤ w - S.val (S.pick w) ∧ w - S.val (S.pick w) ≤ S.U := by
  set v : ℝ := w - (S.bsel w : ℝ) * S.sq with hv
  have hv0 : 0 ≤ v := by have := S.bsel_mul_le w; linarith
  have hval : w - S.val (S.pick w) = v - (S.asel w : ℝ) := by
    simp only [val, pick]
    rw [hv]; ring
  -- the two cases of the rule
  have hcase : (v ≤ S.U ∧ S.asel w = 0) ∨
      (S.U < v ∧ v - S.U ≤ (S.asel w : ℝ) ∧ (S.asel w : ℝ) < v - S.U + (S.p : ℝ)) := by
    rcases le_or_gt v S.U with hle | hlt
    · exact Or.inl ⟨hle, S.asel_eq_zero (by rw [← hv]; exact hle)⟩
    · refine Or.inr ⟨hlt, ?_, ?_⟩
      · have := S.le_asel w; rw [← hv] at this; linarith
      · have := S.asel_lt (by rw [← hv]; exact hlt); rw [← hv] at this; linarith
  -- the residual
  have hres : 0 ≤ w - S.val (S.pick w) ∧ w - S.val (S.pick w) ≤ S.U := by
    rw [hval]
    rcases hcase with ⟨hle, hz⟩ | ⟨hlt, hlo, hhi⟩
    · rw [hz]; push_cast; constructor <;> linarith
    · have := S.p_le_U; constructor <;> linarith
  -- the `a` digit lies in `Ev`
  have hadvd : S.p ∣ S.asel w := S.asel_dvd w
  have hanonneg : 0 ≤ S.asel w :=
    mul_nonneg S.p_pos.le (le_max_left _ _)
  have hale : S.asel w ≤ S.e := by
    rcases hcase with ⟨-, hz⟩ | ⟨hlt, -, hhi⟩
    · rw [hz]; exact le_of_lt S.e_pos
    · -- `a < v - U + p`, and `v` is bounded either by maximality of `b` or by `w ≤ mU`
      have hvb : v ≤ (S.e : ℝ) + S.U := by
        rcases lt_or_eq_of_le (S.bsel_le w) with hb | hb
        · have hlt' := S.lt_bsel_add hb
          have hexp : ((S.bsel w : ℝ) + (S.p : ℝ)) * S.sq
              = (S.bsel w : ℝ) * S.sq + (S.p : ℝ) * S.sq := by ring
          rw [hexp] at hlt'
          have hgap := S.gap'
          rw [hv]
          linarith
        · have hbe : (S.bsel w : ℝ) = (S.e : ℝ) := by rw [hb]
          have hexp : (S.e : ℝ) * (1 + S.sq) = (S.e : ℝ) + (S.e : ℝ) * S.sq := by ring
          have hU := S.U_def'
          rw [hexp] at hU
          have hmU : (S.m : ℝ) * S.U - S.U = (S.e : ℝ) + (S.e : ℝ) * S.sq := by
            rw [← hU]; ring
          rw [hv, hbe]
          linarith
      have h2 : (S.asel w : ℝ) < (S.e : ℝ) + (S.p : ℝ) := by linarith
      have h3 : S.asel w < S.e + S.p := by exact_mod_cast h2
      obtain ⟨r, hr⟩ := hadvd
      obtain ⟨t, ht⟩ := S.p_dvd_e
      have h4 : S.p * r < S.p * (t + 1) := by
        calc S.p * r < S.e + S.p := by rw [← hr]; exact h3
          _ = S.p * t + S.p := by rw [ht]
          _ = S.p * (t + 1) := by ring
      have h5 : r < t + 1 := lt_of_mul_lt_mul_left h4 S.p_pos.le
      calc S.asel w = S.p * r := hr
        _ ≤ S.p * t := mul_le_mul_of_nonneg_left (by omega) S.p_pos.le
        _ = S.e := ht.symm
  exact ⟨⟨hadvd, hanonneg, hale⟩, ⟨S.bsel_dvd w, S.bsel_nonneg h0, S.bsel_le w⟩, hres⟩
end SZ.Slice
