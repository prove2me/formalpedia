-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P33.fact21
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T15:14:52.541739+00:00
-- url     : https://prove2.me/submissions/c4bbb12c-549b-4c04-ac1f-d30dd836db90

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P33
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Extend50.P33

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted type constructors; local notation only reorders Word's arguments.

local notation "Word" => (fun d r : ℕ =>
  QAlgorithms.Papers.Independent.Information100.P58.Word r d)

local notation "Op" => (fun d r : ℕ =>
  QAlgorithms.Papers.Independent.Information100.P21.Op
    (QAlgorithms.Papers.Independent.Information100.P58.Word r d))

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Gap20.P01 (spechtMatrix)

theorem fact21_bellsq_aux (d n : ℕ) (p L : Fin n) (x z : Fin n → Fin d) :
    (∑ w : Fin n → Fin d,
      (if x p = x L ∧ w p = w L ∧ (∀ i, i ≠ p → i ≠ L → x i = w i) then (1:ℂ) else 0) *
      (if w p = w L ∧ z p = z L ∧ (∀ i, i ≠ p → i ≠ L → w i = z i) then (1:ℂ) else 0)) =
    (d:ℂ) * (if x p = x L ∧ z p = z L ∧ (∀ i, i ≠ p → i ≠ L → x i = z i) then (1:ℂ) else 0) := by
  set g : Fin d → Fin n → Fin d := fun c i => if i = p ∨ i = L then c else x i with hg
  have hgp : ∀ c, g c p = c := fun c => by simp [hg]
  have key : ∀ w : Fin n → Fin d,
      (if x p = x L ∧ w p = w L ∧ (∀ i, i ≠ p → i ≠ L → x i = w i) then (1:ℂ) else 0) *
      (if w p = w L ∧ z p = z L ∧ (∀ i, i ≠ p → i ≠ L → w i = z i) then (1:ℂ) else 0) =
      (∑ c : Fin d, if w = g c then (1:ℂ) else 0) *
      (if x p = x L ∧ z p = z L ∧ (∀ i, i ≠ p → i ≠ L → x i = z i) then (1:ℂ) else 0) := by
    intro w
    rw [Finset.sum_eq_single (w p)]
    · by_cases hw : w = g (w p)
      · have hwL : w p = w L := by
          have := congrFun hw L; rw [this]; simp [hg]
        have hwi : ∀ i, i ≠ p → i ≠ L → w i = x i := by
          intro i h1 h2; have := congrFun hw i; rw [this]; simp [hg, h1, h2]
        rw [if_pos hw]
        by_cases hx : x p = x L ∧ z p = z L ∧ (∀ i, i ≠ p → i ≠ L → x i = z i)
        · rw [if_pos hx, if_pos ⟨hx.1, hwL, fun i h1 h2 => (hwi i h1 h2).symm⟩,
            if_pos ⟨hwL, hx.2.1, fun i h1 h2 => (hwi i h1 h2).trans (hx.2.2 i h1 h2)⟩]
        · rw [if_neg hx]
          by_cases h1 : x p = x L ∧ w p = w L ∧ (∀ i, i ≠ p → i ≠ L → x i = w i)
          · have hn : ¬ (w p = w L ∧ z p = z L ∧ (∀ i, i ≠ p → i ≠ L → w i = z i)) := by
              rintro ⟨_, hz, hwz⟩
              exact hx ⟨h1.1, hz, fun i a b => (h1.2.2 i a b).trans (hwz i a b)⟩
            rw [if_pos h1, if_neg hn]
          · rw [if_neg h1]; simp
      · rw [if_neg hw]
        by_cases h1 : x p = x L ∧ w p = w L ∧ (∀ i, i ≠ p → i ≠ L → x i = w i)
        · exfalso; apply hw; funext i
          by_cases hi1 : i = p
          · subst hi1; simp [hg]
          by_cases hi2 : i = L
          · subst hi2; simp [hg, h1.2.1]
          simp [hg, hi1, hi2, h1.2.2 i hi1 hi2]
        · rw [if_neg h1]; simp
    · intro c _ hc; rw [if_neg]; rintro rfl; exact hc (hgp c).symm
    · simp
  rw [Finset.sum_congr rfl (fun w _ => key w), ← Finset.sum_mul, Finset.sum_comm]
  congr 1
  simp

theorem fact21_swap_aux (d n : ℕ) (p L a : Fin n) (hap : a ≠ p) (haL : a ≠ L) (hpL : p ≠ L)
    (x z : Fin n → Fin d) :
    (∑ w : Fin n → Fin d,
      (if x p = x L ∧ (w ∘ Equiv.swap a p) p = (w ∘ Equiv.swap a p) L ∧
          (∀ i, i ≠ p → i ≠ L → x i = (w ∘ Equiv.swap a p) i) then (1:ℂ) else 0) *
      (if w p = w L ∧ z p = z L ∧ (∀ i, i ≠ p → i ≠ L → w i = z i) then (1:ℂ) else 0)) =
    (if x p = x L ∧ z p = z L ∧ (∀ i, i ≠ p → i ≠ L → x i = z i) then (1:ℂ) else 0) := by
  have sa : Equiv.swap a p a = p := Equiv.swap_apply_left _ _
  have sp : Equiv.swap a p p = a := Equiv.swap_apply_right _ _
  have sL : Equiv.swap a p L = L := Equiv.swap_apply_of_ne_of_ne (Ne.symm haL) (Ne.symm hpL)
  have so : ∀ i, i ≠ a → i ≠ p → Equiv.swap a p i = i :=
    fun i h1 h2 => Equiv.swap_apply_of_ne_of_ne h1 h2
  set w0 : Fin n → Fin d := fun i => if i = p ∨ i = L then z a else z i with hw0
  rw [Finset.sum_eq_single w0]
  · simp only [Function.comp_apply, sa, sp, sL]
    have e1 : w0 a = z a := by simp [hw0, hap, haL]
    have e2 : w0 p = z a := by simp [hw0]
    have e3 : w0 L = z a := by simp [hw0]
    have hB : (w0 p = w0 L ∧ z p = z L ∧ (∀ i, i ≠ p → i ≠ L → w0 i = z i)) ↔ z p = z L := by
      constructor
      · exact fun h => h.2.1
      · intro h; exact ⟨by rw [e2, e3], h, fun i h1 h2 => by simp [hw0, h1, h2]⟩
    have hA : (x p = x L ∧ w0 a = w0 L ∧ (∀ i, i ≠ p → i ≠ L → x i = w0 (Equiv.swap a p i))) ↔
        (x p = x L ∧ (∀ i, i ≠ p → i ≠ L → x i = z i)) := by
      constructor
      · rintro ⟨h1, _, h3⟩
        refine ⟨h1, fun i hi1 hi2 => ?_⟩
        have := h3 i hi1 hi2
        by_cases hia : i = a
        · subst hia; rw [sa, e2] at this; exact this
        · rw [so i hia hi1] at this; rw [this]; simp [hw0, hi1, hi2]
      · rintro ⟨h1, h3⟩
        refine ⟨h1, by rw [e1, e3], fun i hi1 hi2 => ?_⟩
        by_cases hia : i = a
        · subst hia; rw [sa, e2]; exact h3 i hi1 hi2
        · rw [so i hia hi1]; simp [hw0, hi1, hi2]; exact h3 i hi1 hi2
    rw [if_congr hA rfl rfl, if_congr hB rfl rfl]
    rw [ite_zero_mul_ite_zero, mul_one]
    exact if_congr ⟨fun h => ⟨h.1.1, h.2, h.1.2⟩, fun h => ⟨⟨h.1, h.2.2⟩, h.2.1⟩⟩ rfl rfl
  · intro w _ hw
    by_cases h2 : w p = w L ∧ z p = z L ∧ (∀ i, i ≠ p → i ≠ L → w i = z i)
    · rw [if_pos h2, mul_one, if_neg]
      rintro ⟨_, h3, _⟩
      simp only [Function.comp_apply, sp, sL] at h3
      apply hw; funext i
      by_cases hi1 : i = p
      · have : w0 i = z a := by simp [hw0, hi1]
        rw [this, hi1, h2.1, ← h3, h2.2.2 a hap haL]
      by_cases hi2 : i = L
      · have : w0 i = z a := by simp [hw0, hi2]
        rw [this, hi2, ← h3, h2.2.2 a hap haL]
      simp [hw0, hi1, hi2, h2.2.2 i hi1 hi2]
    · rw [if_neg h2, mul_zero]
  · simp

theorem fact21_main (d k : ℕ) (hd : 2 ≤ d) (a : Fin (k+2)) :
    unnormalizedPortBell d (k+2) (Fin.last (k+1)) * portSwap d k a *
      unnormalizedPortBell d (k+2) (Fin.last (k+1)) =
      (if a = Fin.last (k+1) then (d:ℂ) else 1) •
        unnormalizedPortBell d (k+2) (Fin.last (k+1)) := by
  ext x z
  set p : Fin (k+3) := (Fin.last (k+1)).castSucc with hp
  set L : Fin (k+3) := Fin.last (k+2) with hL
  set a' : Fin (k+3) := a.castSucc with ha'
  have hBV : ∀ w, (unnormalizedPortBell d (k+2) (Fin.last (k+1)) * portSwap d k a) x w =
      unnormalizedPortBell d (k+2) (Fin.last (k+1)) x (w ∘ Equiv.swap a' p) := by
    intro w
    rw [Matrix.mul_apply, Finset.sum_eq_single (w ∘ Equiv.swap a' p)]
    · simp [portSwap, Schur.tensorPermutation, ← ha', ← hp]
    · intro y _ hy
      simp [portSwap, Schur.tensorPermutation, ← ha', ← hp, hy]
    · simp
  rw [Matrix.mul_apply]
  simp only [hBV]
  simp only [unnormalizedPortBell, Matrix.smul_apply, smul_eq_mul, ← hp, ← hL]
  have hpL : p ≠ L := by
    rw [hp, hL]; intro h; have := congrArg Fin.val h; simp at this
  by_cases ha : a = Fin.last (k+1)
  · have : a' = p := by rw [ha', hp, ha]
    rw [this, Equiv.swap_self]
    simp only [Equiv.coe_refl, Function.comp_id, if_pos ha]
    exact fact21_bellsq_aux d (k+3) p L x z
  · rw [if_neg ha, one_mul]
    have hap : a' ≠ p := by
      rw [ha', hp]; intro h; exact ha (Fin.castSucc_injective _ h)
    have haL : a' ≠ L := by
      rw [ha', hL]; intro h; have := congrArg Fin.val h; simp at this; omega
    exact fact21_swap_aux d (k+3) p L a' hap haL hpL x z

end QAlgorithms.Papers.Independent.Extend50.P33

open QAlgorithms.Papers.Independent.Extend50.P33 in
theorem solution (d k : ℕ) (hd : 2 ≤ d) (a : Fin (k+2)) :
    unnormalizedPortBell d (k+2) (Fin.last (k+1)) * portSwap d k a *
      unnormalizedPortBell d (k+2) (Fin.last (k+1)) =
      (if a = Fin.last (k+1) then (d:ℂ) else 1) •
        unnormalizedPortBell d (k+2) (Fin.last (k+1)) :=
  fact21_main d k hd a

end
