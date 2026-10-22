-- Prove2me | solution 1 for RetailInfoShare.AFS.integer_comparison
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T13:34:22.958747+00:00
-- url     : https://prove2.me/submissions/e3538e14-ab21-4182-a52d-10c4afb2def7

import Mathlib
import Definitions.Def_RetailInfoShare_AFS_Model
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RetailInfoShare.AFS.IntCmpAux

open RetailInfoShare.AFS

/-- Comparison of sharing gains reduces to a polynomial inequality. -/
lemma gain_lt_iff (P : Params) (hP : P.Standing) (k l : ℕ) :
    sharingGain P k < sharingGain P l ↔
      (k : ℝ) * (2 + P.b * ((l : ℝ) - 1)) ^ 2 < l * (2 + P.b * ((k : ℝ) - 1)) ^ 2 := by
  obtain ⟨hN, hb0, hb1, hs, ht, ha0, ha1⟩ := hP
  have hs' : (0 : ℝ) < P.sig := NNReal.coe_pos.mpr hs
  have ht' : (0 : ℝ) < P.t := NNReal.coe_pos.mpr ht
  have hN' : (0 : ℝ) < P.N := by exact_mod_cast hN
  have hS : (0 : ℝ) < (P.sig : ℝ) + (P.t : ℝ) / P.N := by positivity
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hl : (0 : ℝ) ≤ l := Nat.cast_nonneg l
  have hDk : 0 < 2 + P.b * ((k : ℝ) - 1) := by nlinarith
  have hDl : 0 < 2 + P.b * ((l : ℝ) - 1) := by nlinarith
  unfold sharingGain
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  have hc : 0 < P.alpha * (P.sig : ℝ) ^ 2 * ((P.sig : ℝ) + (P.t : ℝ) / P.N) := by positivity
  have e1 : P.alpha * (k : ℝ) * (P.sig : ℝ) ^ 2 *
      ((2 + P.b * ((l : ℝ) - 1)) ^ 2 * ((P.sig : ℝ) + (P.t : ℝ) / P.N)) =
      (P.alpha * (P.sig : ℝ) ^ 2 * ((P.sig : ℝ) + (P.t : ℝ) / P.N)) *
        ((k : ℝ) * (2 + P.b * ((l : ℝ) - 1)) ^ 2) := by ring
  have e2 : P.alpha * (l : ℝ) * (P.sig : ℝ) ^ 2 *
      ((2 + P.b * ((k : ℝ) - 1)) ^ 2 * ((P.sig : ℝ) + (P.t : ℝ) / P.N)) =
      (P.alpha * (P.sig : ℝ) ^ 2 * ((P.sig : ℝ) + (P.t : ℝ) / P.N)) *
        ((l : ℝ) * (2 + P.b * ((k : ℝ) - 1)) ^ 2) := by ring
  rw [e1, e2]
  exact mul_lt_mul_iff_of_pos_left hc

lemma key_identity (b k l : ℝ) :
    l * (2 + b * (k - 1)) ^ 2 - k * (2 + b * (l - 1)) ^ 2 =
      (l - k) * ((2 - b) ^ 2 - (b * k) * (b * l)) := by ring

/-- Strict increase below the peak `2/b - 1`. -/
lemma gain_strictMono (P : Params) (hP : P.Standing) (k l : ℕ) (hkl : k < l)
    (hl : (l : ℝ) ≤ 2 / P.b - 1) : sharingGain P k < sharingGain P l := by
  have hb0 := hP.2.1
  have hb1 := hP.2.2.1
  rw [gain_lt_iff P hP]
  have hkl' : (k : ℝ) < l := by exact_mod_cast hkl
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hbl : P.b * l ≤ 2 - P.b := by
    have := mul_le_mul_of_nonneg_left hl hb0.le
    rw [mul_sub, mul_div_cancel₀ _ hb0.ne'] at this
    linarith
  have hbk : P.b * k < P.b * l := mul_lt_mul_of_pos_left hkl' hb0
  have hbk0 : 0 ≤ P.b * k := by positivity
  have h1 : (P.b * k) * (P.b * l) < (2 - P.b) ^ 2 := by nlinarith
  have := key_identity P.b k l
  nlinarith

/-- Strict decrease above the peak `2/b - 1`. -/
lemma gain_strictAnti (P : Params) (hP : P.Standing) (k l : ℕ) (hkl : k < l)
    (hk : 2 / P.b - 1 ≤ (k : ℝ)) : sharingGain P l < sharingGain P k := by
  have hb0 := hP.2.1
  have hb1 := hP.2.2.1
  rw [gain_lt_iff P hP]
  have hkl' : (k : ℝ) < l := by exact_mod_cast hkl
  have hbk : 2 - P.b ≤ P.b * k := by
    have := mul_le_mul_of_nonneg_left hk hb0.le
    rw [mul_sub, mul_div_cancel₀ _ hb0.ne'] at this
    linarith
  have hbl : P.b * k < P.b * l := mul_lt_mul_of_pos_left hkl' hb0
  have h2b : 0 ≤ 2 - P.b := by linarith
  have h1 : (2 - P.b) ^ 2 < (P.b * k) * (P.b * l) := by nlinarith
  have := key_identity P.b l k
  nlinarith

end RetailInfoShare.AFS.IntCmpAux

open RetailInfoShare.AFS RetailInfoShare.AFS.IntCmpAux in
theorem solution (P : Params) (hP : P.Standing) :
    (∃ K : ℕ, (K = ⌊mStar P⌋₊ ∨ K = ⌈mStar P⌉₊) ∧ K ≤ P.N ∧
        ∀ K' : ℕ, K' ≤ P.N → sharingGain P K' ≤ sharingGain P K) ∧
    ∀ K : ℕ, K ≤ P.N → (∀ K' : ℕ, K' ≤ P.N → sharingGain P K' ≤ sharingGain P K) →
      K = ⌊mStar P⌋₊ ∨ K = ⌈mStar P⌉₊ := by
  have hb0 := hP.2.1
  have hb1 := hP.2.2.1
  set m := mStar P with hm
  have hmx : m ≤ 2 / P.b - 1 := min_le_left _ _
  have hmN : m ≤ (P.N : ℝ) := min_le_right _ _
  have hm0 : 0 ≤ m := by
    have h1 : 1 ≤ 2 / P.b := by rw [le_div_iff₀ hb0]; linarith
    have h2 : (1 : ℝ) ≤ P.N := by exact_mod_cast hP.1
    rw [hm, mStar]; exact le_min (by linarith) (by linarith)
  have hmcase : m = 2 / P.b - 1 ∨ m = (P.N : ℝ) := by
    rw [hm, mStar]; exact min_choice _ _
  set F := ⌊m⌋₊ with hF
  set C := ⌈m⌉₊ with hC
  have hFm : (F : ℝ) ≤ m := Nat.floor_le hm0
  have hmC : m ≤ (C : ℝ) := Nat.le_ceil m
  have hCF : C ≤ F + 1 := by
    rw [hF, hC]; exact Nat.ceil_le_floor_add_one m
  have hFN : F ≤ P.N := by
    have : (F : ℝ) ≤ P.N := le_trans hFm hmN
    exact_mod_cast this
  have hCN : C ≤ P.N := by rw [hC]; exact Nat.ceil_le.mpr hmN
  have hFx : (F : ℝ) ≤ 2 / P.b - 1 := le_trans hFm hmx
  -- above C (strictly), the peak lies at or below C
  have hCx : ∀ K', C < K' → K' ≤ P.N → 2 / P.b - 1 ≤ (C : ℝ) := by
    intro K' h1 h2
    rcases hmcase with h | h
    · linarith
    · exfalso
      have : (C : ℝ) < K' := by exact_mod_cast h1
      have : (K' : ℝ) ≤ P.N := by exact_mod_cast h2
      have : (P.N : ℝ) ≤ C := h ▸ hmC
      linarith
  -- every K' ≤ N is ≤ max of the two candidates
  have below : ∀ K', K' < F → sharingGain P K' < sharingGain P F := fun K' h =>
    gain_strictMono P hP K' F h hFx
  have above : ∀ K', C < K' → K' ≤ P.N → sharingGain P K' < sharingGain P C := fun K' h h' =>
    gain_strictAnti P hP C K' h (hCx K' h h')
  have trich : ∀ K' : ℕ, K' < F ∨ K' = F ∨ K' = C ∨ C < K' := by
    intro K'; omega
  constructor
  · by_cases hcmp : sharingGain P C ≤ sharingGain P F
    · refine ⟨F, Or.inl rfl, hFN, fun K' hK' => ?_⟩
      rcases trich K' with h | h | h | h
      · exact (below K' h).le
      · rw [h]
      · rw [h]; exact hcmp
      · exact ((above K' h hK').le).trans hcmp
    · push Not at hcmp
      refine ⟨C, Or.inr rfl, hCN, fun K' hK' => ?_⟩
      rcases trich K' with h | h | h | h
      · exact (below K' h).le.trans hcmp.le
      · rw [h]; exact hcmp.le
      · rw [h]
      · exact (above K' h hK').le
  · intro K hK hmax
    rcases trich K with h | h | h | h
    · exact absurd (hmax F hFN) (not_le.mpr (below K h))
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd (hmax C hCN) (not_le.mpr (above K h hK))
