-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.sgE_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:41:13.50169+00:00
-- url     : https://prove2.me/submissions/9e4889b1-d50d-4e22-bc52-431bba94ecf8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CarSumSqZeroOfAnti
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_car_bil
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_car_comm_sum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset
namespace ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
private theorem mem_plusIdx_iff_eq_true {ε : Fin n → Bool} {a : Fin n} :
    a ∈ plusIdx ε ↔ ε a = true := by
  simp [plusIdx]
private theorem mem_minusIdx_iff_eq_false {ε : Fin n → Bool} {a : Fin n} :
    a ∈ minusIdx ε ↔ ε a = false := by
  simp [minusIdx]
private theorem sum_sum_eq_sum_diag_of_offdiag_eq_zero {M ι : Type*} [AddCommMonoid M] (s : Finset ι) (F : ι → ι → M)
    (hF : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → F x y = 0) : ∑ x ∈ s, ∑ y ∈ s, F x y = ∑ x ∈ s, F x x :=
  Finset.sum_congr rfl fun x hx =>
    Finset.sum_eq_single x (fun y hy hyx => hF x hx y hy (Ne.symm hyx)) (fun h => absurd hx h)
private theorem sum_sum_eq_apply_of_eq_zero_off_point {M ι κ : Type*} [AddCommMonoid M] (s : Finset ι) (t : Finset κ)
    (x0 : ι) (y0 : κ) (hx0 : x0 ∈ s) (hy0 : y0 ∈ t) (F : ι → κ → M)
    (hF : ∀ x ∈ s, ∀ y ∈ t, (x ≠ x0 ∨ y ≠ y0) → F x y = 0) :
    ∑ x ∈ s, ∑ y ∈ t, F x y = F x0 y0 := by
  rw [Finset.sum_eq_single x0]
  · exact Finset.sum_eq_single y0 (fun y hy hne => hF x0 hx0 y hy (Or.inr hne)) (fun h => absurd hy0 h)
  · exact fun x hx hne => Finset.sum_eq_zero fun y hy => hF x hx y hy (Or.inl hne)
  · exact fun h => absurd hx0 h
private theorem sgE_eq_sum_minusIdx_of_true (ε : Fin n → Bool) (cp cm : Fin n → Fin n → Module.End ℂ W)
    {a b : Fin n} (ha : ε a = true) (hb : ε b = true) :
    sgE ε cp cm a b = ∑ x ∈ minusIdx ε, cp a x * cm b x := by
  unfold sgE
  rw [if_pos (And.intro ha hb)]
private theorem sgE_eq_neg_sum_plusIdx_of_false (ε : Fin n → Bool) (cp cm : Fin n → Fin n → Module.End ℂ W)
    {a b : Fin n} (ha : ε a = false) (hb : ε b = false) :
    sgE ε cp cm a b = -∑ i ∈ plusIdx ε, cp i b * cm i a := by
  unfold sgE
  have h1 : ¬(ε a = true ∧ ε b = true) := by simp [ha]
  rw [if_neg h1, if_pos (And.intro ha hb)]
end ReciprocityTheory.ChartRestriction.DS
end
end

set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {cp cm : Fin n → Fin n → Module.End ℂ W} (hC : IsCAR cp cm) (ε : Fin n → Bool)
    (a b c d : Fin n) (hab : ε a = ε b) (hcd : ε c = ε d) :
    sgE ε cp cm a b * sgE ε cp cm c d - sgE ε cp cm c d * sgE ε cp cm a b =
      (if b = c then sgE ε cp cm a d else 0) - (if d = a then sgE ε cp cm c b else 0) := by
  by_cases ha : ε a = true <;> by_cases hc : ε c = true
  · have hb : ε b = true := by rw [← hab]; exact ha
    have hd : ε d = true := by rw [← hcd]; exact hc
    rw [sgE_eq_sum_minusIdx_of_true ε cp cm ha hb, sgE_eq_sum_minusIdx_of_true ε cp cm hc hd,
      sgE_eq_sum_minusIdx_of_true ε cp cm ha hd, sgE_eq_sum_minusIdx_of_true ε cp cm hc hb]
    simp only [car_comm_sum, car_bil hC]
    refine (sum_sum_eq_sum_diag_of_offdiag_eq_zero _ _ ?_).trans ?_
    · intro x _ y _ hxy
      simp [hxy, Ne.symm hxy]
    · rcases eq_or_ne b c with h1 | h1 <;> rcases eq_or_ne d a with h2 | h2
      · subst h1; subst h2; simp [Finset.sum_sub_distrib]
      · subst h1; simp [h2]
      · subst h2; simp [h1]
      · simp [h1, h2]
  · have hc' : ε c = false := by simpa using hc
    have hb : ε b = true := by rw [← hab]; exact ha
    have hd : ε d = false := by rw [← hcd]; exact hc'
    have hbc : b ≠ c := fun h => by simp [h, hc'] at hb
    have hda : d ≠ a := fun h => by simp [h, ha] at hd
    rw [if_neg hbc, if_neg hda, sub_zero, sgE_eq_sum_minusIdx_of_true ε cp cm ha hb,
      sgE_eq_neg_sum_plusIdx_of_false ε cp cm hc' hd]
    have e1 : ∑ x ∈ minusIdx ε, ∑ i ∈ plusIdx ε,
        (if b = i ∧ x = d then cp a x * cm i c else 0) = cp a d * cm b c := by
      refine (sum_sum_eq_apply_of_eq_zero_off_point _ _ d b (mem_minusIdx_iff_eq_false.mpr hd) (mem_plusIdx_iff_eq_true.mpr hb) _ ?_).trans ?_
      · intro x _ i _ hne
        rw [if_neg]
        rintro ⟨rfl, rfl⟩
        simp at hne
      · simp
    have e2 : ∑ x ∈ minusIdx ε, ∑ i ∈ plusIdx ε,
        (if i = a ∧ c = x then cp i d * cm b x else 0) = cp a d * cm b c := by
      refine (sum_sum_eq_apply_of_eq_zero_off_point _ _ c a (mem_minusIdx_iff_eq_false.mpr hc') (mem_plusIdx_iff_eq_true.mpr ha) _ ?_).trans ?_
      · intro x _ i _ hne
        rw [if_neg]
        rintro ⟨rfl, rfl⟩
        simp at hne
      · simp
    have key : (∑ x ∈ minusIdx ε, cp a x * cm b x) * (∑ i ∈ plusIdx ε, cp i d * cm i c) -
        (∑ i ∈ plusIdx ε, cp i d * cm i c) * (∑ x ∈ minusIdx ε, cp a x * cm b x) = 0 := by
      simp only [car_comm_sum, car_bil hC, Finset.sum_sub_distrib, e1, e2, sub_self]
    rw [mul_neg, neg_mul, neg_sub_neg, ← neg_sub, key, neg_zero]
  · have ha' : ε a = false := by simpa using ha
    have hb : ε b = false := by rw [← hab]; exact ha'
    have hd : ε d = true := by rw [← hcd]; exact hc
    have hbc : b ≠ c := fun h => by simp [h, hc] at hb
    have hda : d ≠ a := fun h => by simp [h, ha'] at hd
    rw [if_neg hbc, if_neg hda, sub_zero, sgE_eq_neg_sum_plusIdx_of_false ε cp cm ha' hb,
      sgE_eq_sum_minusIdx_of_true ε cp cm hc hd]
    have e1 : ∑ i ∈ plusIdx ε, ∑ y ∈ minusIdx ε,
        (if i = c ∧ a = y then cp i b * cm d y else 0) = cp c b * cm d a := by
      refine (sum_sum_eq_apply_of_eq_zero_off_point _ _ c a (mem_plusIdx_iff_eq_true.mpr hc) (mem_minusIdx_iff_eq_false.mpr ha') _ ?_).trans ?_
      · intro i _ y _ hne
        rw [if_neg]
        rintro ⟨rfl, rfl⟩
        simp at hne
      · simp
    have e2 : ∑ i ∈ plusIdx ε, ∑ y ∈ minusIdx ε,
        (if d = i ∧ y = b then cp c y * cm i a else 0) = cp c b * cm d a := by
      refine (sum_sum_eq_apply_of_eq_zero_off_point _ _ d b (mem_plusIdx_iff_eq_true.mpr hd) (mem_minusIdx_iff_eq_false.mpr hb) _ ?_).trans ?_
      · intro i _ y _ hne
        rw [if_neg]
        rintro ⟨rfl, rfl⟩
        simp at hne
      · simp
    have key : (∑ i ∈ plusIdx ε, cp i b * cm i a) * (∑ y ∈ minusIdx ε, cp c y * cm d y) -
        (∑ y ∈ minusIdx ε, cp c y * cm d y) * (∑ i ∈ plusIdx ε, cp i b * cm i a) = 0 := by
      simp only [car_comm_sum, car_bil hC, Finset.sum_sub_distrib, e1, e2, sub_self]
    rw [neg_mul, mul_neg, neg_sub_neg, ← neg_sub, key, neg_zero]
  · have ha' : ε a = false := by simpa using ha
    have hc' : ε c = false := by simpa using hc
    have hb : ε b = false := by rw [← hab]; exact ha'
    have hd : ε d = false := by rw [← hcd]; exact hc'
    rw [sgE_eq_neg_sum_plusIdx_of_false ε cp cm ha' hb, sgE_eq_neg_sum_plusIdx_of_false ε cp cm hc' hd,
      sgE_eq_neg_sum_plusIdx_of_false ε cp cm ha' hd, sgE_eq_neg_sum_plusIdx_of_false ε cp cm hc' hb, neg_mul_neg, neg_mul_neg]
    simp only [car_comm_sum, car_bil hC]
    refine (sum_sum_eq_sum_diag_of_offdiag_eq_zero _ _ ?_).trans ?_
    · intro x _ y _ hxy
      simp [hxy, Ne.symm hxy]
    · rcases eq_or_ne b c with h1 | h1 <;> rcases eq_or_ne d a with h2 | h2
      · subst h1; subst h2; simp [Finset.sum_sub_distrib]; try abel
      · subst h1; simp [h2, Ne.symm h2]; try abel
      · subst h2; simp [h1, Ne.symm h1]; try abel
      · simp [h1, Ne.symm h1, h2, Ne.symm h2]
end ReciprocityTheory.ChartRestriction.DS
