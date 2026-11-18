-- Prove2me | solution 1 for TopDownParity1043.Main.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T15:10:59.905895+00:00
-- url     : https://prove2.me/submissions/4bc30d80-f037-4262-b515-e116b97f01cb

import Mathlib
import Definitions.Def_TopDownParity1043_Main_Subcubes

set_option autoImplicit false
open TopDownParity1043.Main

private theorem reciprocal_fibre_bound {α β : Type} [DecidableEq α] [Fintype β]
    [DecidableEq β] (X : Finset α) (q : α → β) :
    (∑ x ∈ X, (1 : ℝ) / (X.filter fun y => q y = q x).card) ≤ Fintype.card β := by
  classical
  rw [← Finset.sum_fiberwise' X q
    (fun z => (1 : ℝ) / (X.filter fun y => q y = z).card)]
  calc
    ∑ z : β, ∑ x ∈ X.filter (fun y => q y = z),
        (1 : ℝ) / (X.filter fun y => q y = z).card
        ≤ ∑ _ : β, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro z hz
      simp only [Finset.sum_const, nsmul_eq_mul]
      by_cases hc : (X.filter fun y => q y = z).card = 0
      · simp [hc]
      · have hcr : ((X.filter fun y => q y = z).card : ℝ) ≠ 0 := by exact_mod_cast hc
        simp [hcr]
    _ = Fintype.card β := by simp

private theorem log_fibre_bound {α β : Type} [DecidableEq α] [Fintype β]
    [DecidableEq β] [Nonempty β] (X : Finset α) (hX : X.Nonempty) (q : α → β) :
    (X.card : ℝ) * Real.log ((X.card : ℝ) / Fintype.card β) ≤
      ∑ x ∈ X, Real.log ((X.filter fun y => q y = q x).card : ℝ) := by
  classical
  let K : ℝ := (X.card : ℝ) / Fintype.card β
  have hxpos : (0 : ℝ) < X.card := by exact_mod_cast hX.card_pos
  have hbpos : (0 : ℝ) < Fintype.card β := by exact_mod_cast Fintype.card_pos
  have hK : 0 < K := div_pos hxpos hbpos
  have hcount : ∀ x ∈ X, (0 : ℝ) < (X.filter fun y => q y = q x).card := by
    intro x hx
    exact_mod_cast (Finset.card_pos.mpr ⟨x, by simp [hx]⟩)
  have hrecip := reciprocal_fibre_bound X q
  have hsum : 0 ≤ ∑ x ∈ X,
      (Real.log ((X.filter fun y => q y = q x).card : ℝ) - Real.log K) := by
    calc
      0 ≤ (X.card : ℝ) - K * ∑ x ∈ X,
          (1 : ℝ) / (X.filter fun y => q y = q x).card := by
        have hh := mul_le_mul_of_nonneg_left hrecip hK.le
        have hKB : K * Fintype.card β = X.card := by dsimp [K]; field_simp
        nlinarith
      _ = ∑ x ∈ X,
          (1 - (((X.filter fun y => q y = q x).card : ℝ) / K)⁻¹) := by
        simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one,
          div_inv_eq_mul, inv_div, one_div, Finset.mul_sum]
        congr 1
      _ ≤ ∑ x ∈ X,
          (Real.log ((X.filter fun y => q y = q x).card : ℝ) - Real.log K) := by
        apply Finset.sum_le_sum
        intro x hx
        have ht := Real.one_sub_inv_le_log_of_pos (div_pos (hcount x hx) hK)
        rwa [Real.log_div (hcount x hx).ne' hK.ne'] at ht
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at hsum
  exact sub_nonneg.mp hsum

theorem solution (V : Type) [Fintype V] [DecidableEq V]
    (X : Finset (V → Bool)) (hX : X.Nonempty) (S : Finset V) :
    uniformSetMean X (fun x => setDeficit S.card (fibre X x S)) ≤
      setDeficit (Fintype.card V) X := by
  classical
  let q : (V → Bool) → ((Sᶜ : Finset V) → Bool) := project Sᶜ
  have hfib : ∀ x : V → Bool, (X.filter fun y => q y = q x) = fibre X x S := by
    intro x
    ext y
    simp only [fibre, Finset.mem_filter]
    apply and_congr_right
    intro hy
    constructor
    · intro he i hi
      exact congrFun he ⟨i, Finset.mem_compl.mpr hi⟩
    · intro he
      funext i
      exact he i.1 (Finset.mem_compl.mp i.2)
  have hlog := log_fibre_bound X hX q
  simp only [hfib] at hlog
  have hc : Fintype.card ((Sᶜ : Finset V) → Bool) = 2 ^ (Fintype.card V - S.card) := by simp
  rw [hc] at hlog
  have hnpos : (0 : ℝ) < X.card := by exact_mod_cast hX.card_pos
  have hpowpos : (0 : ℝ) < 2 ^ (Fintype.card V - S.card) := by positivity
  push_cast at hlog
  rw [Real.log_div hnpos.ne' hpowpos.ne', Real.log_pow] at hlog
  have hdim : ((Fintype.card V - S.card : ℕ) : ℝ) =
      (Fintype.card V : ℝ) - S.card := by
    exact_mod_cast Nat.cast_sub (Finset.card_le_univ S)
  rw [hdim] at hlog
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold uniformSetMean setDeficit
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, Real.logb,
    ← Finset.sum_div]
  apply (div_le_iff₀ hnpos).mpr
  apply (mul_le_mul_iff_of_pos_right hlogtwo).mp
  field_simp at *
  nlinarith [hlog]
