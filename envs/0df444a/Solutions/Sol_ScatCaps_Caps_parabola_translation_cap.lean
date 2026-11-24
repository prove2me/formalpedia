-- Prove2me | solution 1 for ScatCaps.Caps.parabola_translation_cap
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T00:01:55.498221+00:00
-- url     : https://prove2.me/submissions/bdf04417-d529-43ff-8967-efcbdbc319b2

import Mathlib
import Definitions.Def_ScatCaps_Caps_Model

open ScatCaps.Caps

theorem solution (K : Type*) [Field K] [Fintype K] (t : ℕ)
    (hK : Fintype.card K = 2 ^ t) :
    IsTranslationCap (parabola K) := by
  have h2 : (2 : K) = 0 := by
    have hc := FiniteField.cast_card_eq_zero K
    rw [hK] at hc
    push_cast at hc
    exact eq_zero_of_pow_eq_zero hc
  refine ⟨?_, ⟨{ carrier := parabola K, add_mem' := ?_, zero_mem' := ?_, neg_mem' := ?_ }, rfl⟩⟩
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ _ ⟨z, rfl⟩ hxy hxz hyz hcol
    have hxy' : x ≠ y := fun h => hxy (by rw [h])
    have hxz' : x ≠ z := fun h => hxz (by rw [h])
    have hyz' : y ≠ z := fun h => hyz (by rw [h])
    rw [collinear_iff_of_mem (Set.mem_insert _ _)] at hcol
    obtain ⟨v, hv⟩ := hcol
    obtain ⟨r, hr⟩ := hv _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    obtain ⟨s, hs⟩ := hv _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
    have r0 := congrFun hr 0
    have r1 := congrFun hr 1
    have s0 := congrFun hs 0
    have s1 := congrFun hs 1
    simp only [vadd_eq_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
      Matrix.cons_val_one] at r0 r1 s0 s1
    have hr0 : r ≠ 0 := by
      rintro rfl
      apply hxy'
      linear_combination -r0
    have hs0 : s ≠ 0 := by
      rintro rfl
      apply hxz'
      linear_combination -s0
    have hv0 : v 0 ≠ 0 := by
      intro h0
      apply hxy'
      rw [h0, mul_zero, zero_add] at r0
      exact r0.symm
    have e1 : r * (v 1 - v 0 * (y + x)) = 0 := by linear_combination (y + x) * r0 - r1
    have e2 : s * (v 1 - v 0 * (z + x)) = 0 := by linear_combination (z + x) * s0 - s1
    have f1 := sub_eq_zero.mp ((mul_eq_zero.mp e1).resolve_left hr0)
    have f2 := sub_eq_zero.mp ((mul_eq_zero.mp e2).resolve_left hs0)
    have e3 : v 0 * (y - z) = 0 := by linear_combination f2 - f1
    exact hyz' (sub_eq_zero.mp ((mul_eq_zero.mp e3).resolve_left hv0))
  · rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    refine ⟨x + y, ?_⟩
    ext i
    fin_cases i
    · simp
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, Pi.add_apply]
      linear_combination (x * y) * h2
  · exact ⟨0, by ext i; fin_cases i <;> simp⟩
  · rintro _ ⟨x, rfl⟩
    refine ⟨-x, ?_⟩
    ext i
    fin_cases i
    · simp
    · simp
      linear_combination x ^ 2 * h2
