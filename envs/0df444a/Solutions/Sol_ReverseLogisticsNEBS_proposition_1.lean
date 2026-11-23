-- Prove2me | solution 1 for ReverseLogisticsNEBS.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T00:11:12.242639+00:00
-- url     : https://prove2.me/submissions/d4f46da6-a199-46fa-ae11-2ba577c321bc

import Mathlib
import Definitions.Def_ReverseLogisticsNEBS_Inst

set_option autoImplicit false

open MeasureTheory ReverseLogisticsNEBS

theorem solution {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] [Countable Ω]
    [MeasurableSingletonClass Ω] (M : Model N Ω) (hM : M.Standing) (t : ℕ)
    (G : Ω → (Fin N → ℝ) → ℝ) (ω : Ω) (x : Fin N → ℝ) (hx : ∀ j : Fin N, 0 < j.val → 0 ≤ x j)
    (relaxed : Bool) (a : Inst N) (ha : Inst.Feas relaxed x a) :
    (∀ j, 0 ≤ a.semiReduce.XE j ∧ 0 ≤ a.semiReduce.XR j ∧ 0 ≤ a.semiReduce.X j) ∧
    (∀ j, a.semiReduce.XE j = 0 ∨ a.semiReduce.XR j = 0) ∧
    (∀ j, a.semiReduce.XE j ≤ a.XE j ∧ a.semiReduce.XR j ≤ a.XR j) ∧
    Inst.Feas relaxed x a.semiReduce ∧
    (∀ d, Inst.next x a.semiReduce d = Inst.next x a d) ∧
    M.instObj t G ω x a.semiReduce ≤ M.instObj t G ω x a ∧
    ((∃ j, 0 < a.XE j ∧ 0 < a.XR j ∧ 0 < M.cE j) →
      M.instObj t G ω x a.semiReduce < M.instObj t G ω x a) := by
  obtain ⟨hXE0, hXR0, hX0, hc1, hc2, hc3, hc4⟩ := ha
  have hmax1 : ∀ p q : ℝ, max (p - q) 0 = p - min p q := by
    intro p q
    rcases le_total p q with h | h
    · rw [max_eq_right (by linarith), min_eq_left h]; ring
    · rw [max_eq_left (by linarith), min_eq_right h]
  have hmax2 : ∀ p q : ℝ, max (q - p) 0 = q - min p q := by
    intro p q
    rcases le_total p q with h | h
    · rw [max_eq_left (by linarith), min_eq_left h]
    · rw [max_eq_right (by linarith), min_eq_right h]; ring
  have hE : ∀ j, a.semiReduce.XE j = a.XE j - min (a.XE j) (a.XR j) := fun j => hmax1 _ _
  have hR : ∀ j, a.semiReduce.XR j = a.XR j - min (a.XE j) (a.XR j) := fun j => hmax2 _ _
  have hXs : a.semiReduce.X = a.X := rfl
  have hmin0 : ∀ j, 0 ≤ min (a.XE j) (a.XR j) := fun j => le_min (hXE0 j) (hXR0 j)
  have hminE : ∀ j, min (a.XE j) (a.XR j) ≤ a.XE j := fun j => min_le_left _ _
  have hminR : ∀ j, min (a.XE j) (a.XR j) ≤ a.XR j := fun j => min_le_right _ _
  have hnext : ∀ d, Inst.next x a.semiReduce d = Inst.next x a d := by
    intro d
    funext j
    simp only [Inst.next, Inst.below, hE, hR, hXs]
    split_ifs <;> ring
  have hcE : ∀ j, 0 ≤ M.cE j := by
    intro j
    simp only [Model.cE]
    have h1 := hM.k_pos j
    have h2 := hM.k_le_kE j
    by_cases hj : j.val + 1 < N
    · have := hM.kR_pos j hj
      linarith
    · have := hM.k_top j (by omega)
      linarith
  have hgam : firstLoc x + firstLoc a.semiReduce.XE - firstLoc a.semiReduce.XR =
      firstLoc x + firstLoc a.XE - firstLoc a.XR := by
    unfold firstLoc
    split_ifs
    · rw [hE, hR]; ring
    · ring
  have hint : (∫ z, G z.2 (Inst.next x a.semiReduce z.1) ∂(M.κ t ω)) =
      ∫ z, G z.2 (Inst.next x a z.1) ∂(M.κ t ω) := by
    simp only [hnext]
  have hterm : ∀ j, (M.kE j + M.h j) * a.semiReduce.XE j + (M.kR j - M.h j) * a.semiReduce.XR j +
      M.k j * a.semiReduce.X j + M.H j * x j =
      ((M.kE j + M.h j) * a.XE j + (M.kR j - M.h j) * a.XR j + M.k j * a.X j + M.H j * x j) -
        M.cE j * min (a.XE j) (a.XR j) := by
    intro j
    rw [hE j, hR j, hXs]
    simp only [Model.cE]
    ring
  have hobj : M.instObj t G ω x a.semiReduce =
      M.instObj t G ω x a - ∑ j, M.cE j * min (a.XE j) (a.XR j) := by
    unfold Model.instObj
    rw [hgam, hint, Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_sub_distrib]
    ring
  refine ⟨fun j => ⟨le_max_right _ _, le_max_right _ _, hX0 j⟩, ?_, ?_, ?_, hnext, ?_, ?_⟩
  · intro j
    rcases le_total (a.XE j) (a.XR j) with h | h
    · left; rw [hE, min_eq_left h, sub_self]
    · right; rw [hR, min_eq_right h, sub_self]
  · intro j
    rw [hE, hR]
    exact ⟨by linarith [hmin0 j], by linarith [hmin0 j]⟩
  · refine ⟨fun j => le_max_right _ _, fun j => le_max_right _ _, hX0, ?_, ?_, ?_, ?_⟩
    · intro i j hij
      rw [hE, hE]
      have := hc3 i j hij
      linarith [hminR i, hmin0 j]
    · intro j hj
      have h2 := hc2 j hj
      rw [hR, hE]
      rcases le_total (a.XE j) (a.XR j) with h | h
      · rw [min_eq_left h, sub_self, add_zero]
        rcases le_total 0 (x j + a.XE j) with h' | h'
        · rw [max_eq_left h'] at h2
          exact le_max_of_le_left (by linarith)
        · rw [max_eq_right h'] at h2
          exact le_max_of_le_right (by linarith [hXE0 j])
      · rw [min_eq_right h, sub_self]
        exact le_max_right _ _
    · intro i j hij
      rw [hR, hE, hE]
      have := hc3 i j hij
      linarith [hmin0 j]
    · intro i j hij
      have h4 := hc4 i j hij
      rw [hR i, hE i, hE j, hXs]
      cases relaxed
      · simp only [Bool.false_eq_true, if_false] at h4 ⊢
        linarith [hmin0 j]
      · simp only [if_true] at h4 ⊢
        rw [hR j]
        linarith
  · rw [hobj]
    have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => mul_nonneg (hcE j) (hmin0 j))
    linarith
  · rintro ⟨j, h1, h2, h3⟩
    rw [hobj]
    have := Finset.sum_pos' (fun j (_ : j ∈ Finset.univ) => mul_nonneg (hcE j) (hmin0 j))
      ⟨j, Finset.mem_univ _, mul_pos h3 (lt_min h1 h2)⟩
    linarith
