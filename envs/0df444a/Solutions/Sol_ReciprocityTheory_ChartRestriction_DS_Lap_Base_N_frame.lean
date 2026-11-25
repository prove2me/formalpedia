-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Base.N.frame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:27:39.47573+00:00
-- url     : https://prove2.me/submissions/3ce49c82-ae68-4284-86c3-4f44babe1baf

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_LaplaceFoundations_OneParameterSubgroups_ExistsCyclic
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Base_N_formV_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Base_N_exists_cyclic
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Base_N_exists_dual
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Base_N_formV_sub_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.Base ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
theorem _root_.solution (r : ℕ) (x : Fin (2 * r + 1) → ℝ) (hx : StrictAnti x) :
    ∃ (e f : Fin r → Fin (2 * r + 1) → ℝ) (z : Fin (2 * r + 1) → ℝ),
      (∀ a b, formV (e a) (e b) = 0) ∧ (∀ a b, formV (f a) (f b) = 0) ∧
      (∀ a b, formV (f a) (e b) = if a = b then 1 else 0) ∧
      (∀ a, formV (e a) z = 0) ∧ (∀ a, formV (f a) z = 0) ∧ formV z z = -1 ∧
      (∀ a s, x s * e a s = if h : a.val + 1 < r then e ⟨a.val + 1, h⟩ s else z s) := by
  classical
  obtain ⟨c, hc0, hc⟩ := exists_cyclic r x hx
  let g : ℕ → Fin (2 * r + 1) → ℝ := fun i s => x s ^ i * c s
  have hG : ∀ i j : ℕ, i + j ≤ 2 * r →
      formV (g i) (g j) = if i + j = 2 * r then -1 else 0 := hc
  have hdual : ∀ a : Fin r, ∃ v : Fin (2 * r + 1) → ℝ, ∀ i : Fin (2 * r + 1),
      formV v (g i.val) = if i.val = a.val then 1 else 0 := fun a =>
    exists_dual x c hx.injective hc0 _
  choose f' hf' using hdual
  let e : Fin r → Fin (2 * r + 1) → ℝ := fun a => g a.val
  let z : Fin (2 * r + 1) → ℝ := g r
  let Q : Fin r → Fin r → ℝ := fun a b => formV (f' a) (f' b)
  let f : Fin r → Fin (2 * r + 1) → ℝ := fun a s => f' a s - ∑ b, (1 / 2 * Q a b) * e b s
  have hee : ∀ a b : Fin r, formV (e a) (e b) = 0 := by
    intro a b
    have := a.isLt
    have := b.isLt
    change formV (g a.val) (g b.val) = 0
    rw [hG _ _ (by omega), if_neg (by omega)]
  have hez : ∀ a : Fin r, formV (e a) z = 0 := by
    intro a
    have := a.isLt
    change formV (g a.val) (g r) = 0
    rw [hG _ _ (by omega), if_neg (by omega)]
  have hzz : formV z z = -1 := by
    change formV (g r) (g r) = -1
    rw [hG _ _ (by omega), if_pos (by omega)]
  have hf'e : ∀ a b : Fin r, formV (f' a) (e b) = if a = b then 1 else 0 := by
    intro a b
    have h := hf' a ⟨b.val, by omega⟩
    change formV (f' a) (g b.val) = _
    rw [show formV (f' a) (g b.val) = if b.val = a.val then 1 else 0 from h]
    by_cases hab : a = b
    · subst hab
      simp
    · rw [if_neg (fun h' => hab (Fin.ext h'.symm)), if_neg hab]
  have hf'z : ∀ a : Fin r, formV (f' a) z = 0 := by
    intro a
    have := a.isLt
    have h := hf' a ⟨r, by omega⟩
    change formV (f' a) (g r) = 0
    rw [show formV (f' a) (g r) = if r = a.val then 1 else 0 from h, if_neg (by omega)]
  have hfe : ∀ a b : Fin r, formV (f a) (e b) = if a = b then 1 else 0 := by
    intro a b
    have h1 : formV (f a) (e b) = formV (f' a) (e b) - ∑ c, (1 / 2 * Q a c) * formV (e c) (e b) :=
      formV_sub_sum _ _ _ _
    rw [h1, hf'e]
    simp [hee]
  have hfz : ∀ a : Fin r, formV (f a) z = 0 := by
    intro a
    have h1 : formV (f a) z = formV (f' a) z - ∑ c, (1 / 2 * Q a c) * formV (e c) z :=
      formV_sub_sum _ _ _ _
    rw [h1, hf'z]
    simp [hez]
  have hff : ∀ a b : Fin r, formV (f a) (f b) = 0 := by
    intro a b
    have h1 : formV (f a) (f b) = formV (f' a) (f b) - ∑ c, (1 / 2 * Q a c) * formV (e c) (f b) :=
      formV_sub_sum _ _ _ _
    have h2 : formV (f' a) (f b) = Q b a - ∑ d, (1 / 2 * Q b d) * formV (e d) (f' a) := by
      rw [formV_symm]
      exact formV_sub_sum _ _ _ _
    have h3 : ∀ c, formV (e c) (f b) = if b = c then 1 else 0 := fun c => by
      rw [formV_symm, hfe]
    have h4 : ∀ d, formV (e d) (f' a) = if a = d then 1 else 0 := fun d => by
      rw [formV_symm, hf'e]
    rw [h1, h2]
    simp only [h3, h4, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have hQ : Q b a = Q a b := formV_symm _ _
    rw [hQ]
    ring
  refine ⟨e, f, z, hee, hff, hfe, hez, hfz, hzz, fun a s => ?_⟩
  change x s * (x s ^ a.val * c s) = if h : a.val + 1 < r then g (a.val + 1) s else g r s
  split_ifs with h
  · ring
  · have hr : a.val + 1 = r := by omega
    have hp : x s ^ r = x s ^ (a.val + 1) := by rw [hr]
    change x s * (x s ^ a.val * c s) = x s ^ r * c s
    rw [hp]
    ring
end ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
