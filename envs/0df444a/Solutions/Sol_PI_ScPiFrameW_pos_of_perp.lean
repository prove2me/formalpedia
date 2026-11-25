-- Prove2me | solution 1 for PI.ScPiFrameW.pos_of_perp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:49:01.4212+00:00
-- url     : https://prove2.me/submissions/c3614f86-0d29-4014-8bf8-7c60c3e689b8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianFrameExistence_HJSumSmulRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianFrameExistence_PosOfPerp
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_ScPiFrameW_exists_rel
import Theorems.Thm_PI_ScPiFrameW_hJ_conj
import Theorems.Thm_PI_ScPiFrameW_hJ_self_re
import Theorems.Thm_PI_ScPiFrameW_hJ_sub_left
import Theorems.Thm_PI_ScPiFrameW_hJ_sub_right
import Theorems.Thm_PI_ScPiFrameW_hJ_sum_smul_left
import Theorems.Thm_PI_ScPiFrameW_hJ_sum_smul_right
import Theorems.Thm_PI_ScPiFrameW_re_star_mul_mul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


section
noncomputable section
open Matrix
namespace PI.ScPiFrameW
open PI.ScPiExists
variable {n : ℕ}
private theorem nonneg_term_lemma (ε : Fin n → Bool) {r : ℕ} (σ : Fin (r + 1) → Fin n)
    (hσ : ∀ i, ε i = false → ∃ j, σ j = i) (w : Fin n → ℂ) (hw0 : ∀ j, w (σ j) = 0) (i : Fin n) :
    0 ≤ (if ε i then (1 : ℝ) else -1) * Complex.normSq (w i) := by
  cases hi : ε i
  · obtain ⟨k, hk⟩ := hσ i hi
    subst hk
    simp [hw0]
  · simp [Complex.normSq_nonneg]
private theorem pos_of_vanish_lemma_2 (ε : Fin n → Bool) {r : ℕ} (σ : Fin (r + 1) → Fin n)
    (hσ : ∀ i, ε i = false → ∃ j, σ j = i) (w : Fin n → ℂ) (hw0 : ∀ j, w (σ j) = 0)
    (hw : w ≠ 0) : 0 < (hJ ε w w).re := by
  rw [hJ_self_re]
  obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hw (funext h)
  have hεi : ε i = true := by
    cases hj : ε i
    · obtain ⟨k, hk⟩ := hσ i hj
      exact (hi (by rw [← hk]; exact hw0 k)).elim
    · rfl
  calc (0 : ℝ) < (if ε i then (1 : ℝ) else -1) * Complex.normSq (w i) := by
        rw [if_pos hεi, one_mul]
        exact Complex.normSq_pos.mpr hi
    _ ≤ ∑ j, (if ε j then (1 : ℝ) else -1) * Complex.normSq (w j) :=
        Finset.single_le_sum (fun j _ => nonneg_term_lemma ε σ hσ w hw0 j) (Finset.mem_univ i)
end PI.ScPiFrameW
end
end

set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.ScPiFrameW
open PI.ScPiExists
variable {n : ℕ}
namespace PI.ScPiFrameW
theorem _root_.solution (ε : Fin n → Bool) {r : ℕ} (σ : Fin (r + 1) → Fin n)
    (hσ : ∀ i, ε i = false → ∃ j, σ j = i)
    (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (t : ℝ) (ht : 0 < t)
    (hee : ∀ a b, hJ ε (e a) (e b) = 0) (hff : ∀ a b, hJ ε (f a) (f b) = 0)
    (hef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0)
    (hez : ∀ a, hJ ε (e a) z = 0) (hfz : ∀ a, hJ ε (f a) z = 0) (hzz : hJ ε z z = -(t : ℂ))
    (y : Fin n → ℂ) (hey : ∀ c, hJ ε (e c) y = 0) (hfy : ∀ c, hJ ε (f c) y = 0)
    (hzy : hJ ε z y = 0) (hy : y ≠ 0) : 0 < (hJ ε y y).re := by
  by_contra hcon
  have hle : (hJ ε y y).re ≤ 0 := not_lt.mp hcon
  obtain ⟨m, hm⟩ : ∃ m : Fin r ⊕ Bool → Fin n → ℂ,
      m = Sum.elim (fun a => e a - f a) (fun b => if b then y else z) := ⟨_, rfl⟩
  have hmi : ∀ a, m (Sum.inl a) = e a - f a := fun a => by rw [hm]; rfl
  have hmf : m (Sum.inr false) = z := by rw [hm]; rfl
  have hmt : m (Sum.inr true) = y := by rw [hm]; rfl
  obtain ⟨D, hD⟩ : ∃ D : Fin r ⊕ Bool → ℂ,
      D = Sum.elim (fun _ => (-2 : ℂ)) (fun b => if b then hJ ε y y else -(t : ℂ)) := ⟨_, rfl⟩
  have hDi : ∀ a, D (Sum.inl a) = -2 := fun a => by rw [hD]; rfl
  have hDf : D (Sum.inr false) = -(t : ℂ) := by rw [hD]; rfl
  have hDt : D (Sum.inr true) = hJ ε y y := by rw [hD]; rfl
  have hG : ∀ k l, hJ ε (m k) (m l) = if k = l then D k else 0 := by
    intro k l
    rcases k with a | i <;> rcases l with b | j
    · simp only [hmi, hJ_sub_left, hJ_sub_right, hee, hff, hef, hJ_conj ε (e b) (f a), hDi]
      by_cases hab : a = b
      · subst hab
        norm_num
      · simp [hab, Ne.symm hab]
    · cases j <;> simp [hmi, hmf, hmt, hJ_sub_left, hez, hfz, hey, hfy]
    · cases i <;> simp [hmi, hmf, hmt, hJ_sub_right, hJ_conj ε (e b) z, hJ_conj ε (f b) z,
        hJ_conj ε (e b) y, hJ_conj ε (f b) y, hez, hfz, hey, hfy]
    · cases i <;> cases j <;> simp [hmf, hmt, hDf, hDt, hzz, hzy, hJ_conj ε z y]
  obtain ⟨g, hg, k0, hk0⟩ := exists_rel (fun k : Fin r ⊕ Bool => fun j : Fin (r + 1) => m k (σ j))
    (by simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_bool]; omega)
  obtain ⟨v, hv⟩ : ∃ v : Fin n → ℂ, v = ∑ k, g k • m k := ⟨_, rfl⟩
  have hv0 : ∀ j, v (σ j) = 0 := by
    intro j
    have h := congrFun hg j
    rw [hv]
    simpa [Finset.sum_apply] using h
  have hvv : (hJ ε v v).re = ∑ k, Complex.normSq (g k) * (D k).re := by
    rw [hv, hJ_sum_smul_left, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hJ_sum_smul_right]
    simp only [hG, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact re_star_mul_mul _ _
  have hterm : ∀ k, Complex.normSq (g k) * (D k).re ≤ 0 := by
    intro k
    refine mul_nonpos_iff.mpr (Or.inl ⟨Complex.normSq_nonneg _, ?_⟩)
    rcases k with a | b
    · rw [hDi]
      norm_num
    · cases b
      · rw [hDf]
        simp [ht.le]
      · rw [hDt]
        exact hle
  have hsum : 0 ≤ ∑ k, Complex.normSq (g k) * (D k).re := by
    rw [← hvv, hJ_self_re]
    exact Finset.sum_nonneg fun i _ => nonneg_term_lemma ε σ hσ v hv0 i
  have hzero : ∀ k, Complex.normSq (g k) * (D k).re = 0 := by
    have h0 : ∑ k, Complex.normSq (g k) * (D k).re = 0 :=
      le_antisymm (Finset.sum_nonpos fun k _ => hterm k) hsum
    intro k
    exact (Finset.sum_eq_zero_iff_of_nonpos fun k _ => hterm k).mp h0 k (Finset.mem_univ k)
  have hga : ∀ a, g (Sum.inl a) = 0 := by
    intro a
    simpa [hDi] using hzero (Sum.inl a)
  have hgf : g (Sum.inr false) = 0 := by
    simpa [hDf, ht.ne'] using hzero (Sum.inr false)
  have hvy : v = g (Sum.inr true) • y := by
    rw [hv, Fintype.sum_sum_type, Fintype.sum_bool]
    simp [hga, hgf, hmt]
  have hgt : g (Sum.inr true) ≠ 0 := by
    rcases k0 with a | b
    · exact absurd (hga a) hk0
    · cases b
      · exact absurd hgf hk0
      · exact hk0
  have hy0 : ∀ j, y (σ j) = 0 := by
    intro j
    have h := hv0 j
    rw [hvy, Pi.smul_apply, smul_eq_mul] at h
    exact (mul_eq_zero.mp h).resolve_left hgt
  exact hcon (pos_of_vanish_lemma_2 ε σ hσ y hy0 hy)
end PI.ScPiFrameW
