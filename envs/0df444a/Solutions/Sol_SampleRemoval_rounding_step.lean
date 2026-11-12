-- Prove2me | solution 1 for SampleRemoval.rounding_step
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T23:34:48.571552+00:00
-- url     : https://prove2.me/submissions/a5eb50a3-60ec-439f-a6e2-7fde4dece7a6

import Mathlib
import Definitions.Def_SampleRemoval_ind
import Definitions.Def_SampleRemoval_feasible
import Definitions.Def_SampleRemoval_GeneralPosition
import Theorems.Thm_SampleRemoval_lemma_3_1
import Theorems.Thm_SampleRemoval_gram_posDef_iff_card_support

section
set_option autoImplicit false

open Matrix

namespace SampleRemoval
namespace Dev
namespace Rounding

theorem gram_update_zero {n d : ℕ} (x : Fin n → Fin d → ℝ) (u : Fin n → ℝ) (t : Fin n) :
    gram x (Function.update u t 0) =
      ∑ i ∈ Finset.univ.erase t, u i • Matrix.vecMulVec (x i) (x i) := by
  unfold gram
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ t)]
  simp only [Function.update_self, zero_smul, zero_add]
  exact Finset.sum_congr rfl fun i hi => by
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

theorem pd_of_ones {n d : ℕ} (x : Fin n → Fin d → ℝ) (hGP : GeneralPosition x)
    (v : Fin n → ℝ) (hv : ∀ i, v i ∈ Set.Icc (0 : ℝ) 1)
    (h : d ≤ (Finset.univ.filter (fun i => v i = 1)).card) : (gram x v).PosDef := by
  refine (gram_posDef_iff_card_support x hGP v hv).mpr (le_trans h ?_)
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  rw [hi]; exact one_ne_zero

theorem step {n d : ℕ} (x : Fin n → Fin d → ℝ) (y : Fin n → ℝ) (e : Fin d → ℝ)
    (θ : ℝ) (hGP : GeneralPosition x) :
    ∀ k : ℕ, ∀ u : Fin n → ℝ, u ∈ feasible x y e θ →
      d ≤ (Finset.univ.filter (fun i => u i = 1)).card →
      (Finset.univ.filter (fun i => u i ≠ 0 ∧ u i ≠ 1)).card ≤ k →
      ∃ S : Finset (Fin n), Finset.univ.filter (fun i => u i = 1) ⊆ S ∧
        S ⊆ Finset.univ.filter (fun i => u i ≠ 0) ∧ ind S ∈ feasible x y e θ := by
  intro k
  induction k with
  | zero =>
    intro u hu hI hk
    refine ⟨Finset.univ.filter (fun i => u i = 1), subset_rfl, ?_, ?_⟩
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      rw [hi]; exact one_ne_zero
    · have hu' : u = ind (Finset.univ.filter (fun i => u i = 1)) := by
        funext i
        have hempty := Finset.card_eq_zero.mp (Nat.le_zero.mp hk)
        have hi : ¬ (u i ≠ 0 ∧ u i ≠ 1) := by
          intro h
          have : i ∈ Finset.univ.filter (fun i => u i ≠ 0 ∧ u i ≠ 1) := by simpa using h
          rw [hempty] at this; simp at this
        by_cases h1 : u i = 1
        · simp [ind, h1]
        · have h0 : u i = 0 := by
            by_contra h0; exact hi ⟨h0, h1⟩
          simp [ind, h0, h1]
      rw [← hu']; exact hu
  | succ k ih =>
    intro u hu hI hk
    by_cases hemp : (Finset.univ.filter (fun i => u i ≠ 0 ∧ u i ≠ 1)) = ∅
    · exact ih u hu hI (by rw [hemp]; simp)
    · obtain ⟨t, ht⟩ := Finset.nonempty_iff_ne_empty.mpr hemp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
      obtain ⟨ht0, ht1⟩ := ht
      obtain ⟨hw, hGu, hθ⟩ := hu
      -- G₀ is positive definite
      have hw0 : ∀ i, Function.update u t 0 i ∈ Set.Icc (0 : ℝ) 1 := by
        intro i
        by_cases hi : i = t
        · subst hi; simp
        · rw [Function.update_of_ne hi]; exact hw i
      have hG₀ : (∑ i ∈ Finset.univ.erase t, u i • Matrix.vecMulVec (x i) (x i)).PosDef := by
        rw [← gram_update_zero]
        apply pd_of_ones x hGP _ hw0
        refine le_trans hI (Finset.card_le_card ?_)
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        have hit : i ≠ t := by rintro rfl; exact ht1 hi
        rw [Function.update_of_ne hit]; exact hi
      obtain ⟨_, _, hmono⟩ := lemma_3_1 x y u hw t hG₀
      have hut : u t ∈ Set.Icc (0 : ℝ) 1 := hw t
      have hfu : e ⬝ᵥ ols x y (Function.update u t (u t)) ≤ θ := by
        rw [Function.update_eq_self]; exact hθ
      -- choose the endpoint
      obtain ⟨a, ha, hfa⟩ : ∃ a : ℝ, (a = 0 ∨ a = 1) ∧ e ⬝ᵥ ols x y (Function.update u t a) ≤ θ := by
        rcases hmono e with hm | hm
        · refine ⟨0, Or.inl rfl, le_trans ?_ hfu⟩
          exact hm (by simp) hut hut.1
        · refine ⟨1, Or.inr rfl, le_trans ?_ hfu⟩
          exact hm hut (by simp) hut.2
      set u' := Function.update u t a with hu'
      have hw' : ∀ i, u' i ∈ Set.Icc (0 : ℝ) 1 := by
        intro i
        by_cases hi : i = t
        · subst hi; rw [hu', Function.update_self]; rcases ha with rfl | rfl <;> simp
        · rw [hu', Function.update_of_ne hi]; exact hw i
      have hones : Finset.univ.filter (fun i => u i = 1) ⊆ Finset.univ.filter (fun i => u' i = 1) := by
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        have hit : i ≠ t := by rintro rfl; exact ht1 hi
        rw [hu', Function.update_of_ne hit]; exact hi
      have hI' : d ≤ (Finset.univ.filter (fun i => u' i = 1)).card :=
        le_trans hI (Finset.card_le_card hones)
      have hfeas : u' ∈ feasible x y e θ :=
        ⟨hw', pd_of_ones x hGP u' hw' hI', hfa⟩
      have hfrac : (Finset.univ.filter (fun i => u' i ≠ 0 ∧ u' i ≠ 1)).card ≤ k := by
        have hsub : Finset.univ.filter (fun i => u' i ≠ 0 ∧ u' i ≠ 1) ⊆
            (Finset.univ.filter (fun i => u i ≠ 0 ∧ u i ≠ 1)).erase t := by
          intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase] at hi ⊢
          have hit : i ≠ t := by
            rintro rfl
            rw [hu', Function.update_self] at hi
            rcases ha with rfl | rfl <;> simp at hi
          rw [hu', Function.update_of_ne hit] at hi
          exact ⟨hit, hi⟩
        have := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem (by simpa using And.intro ht0 ht1)] at this
        omega
      obtain ⟨S, hS1, hS2, hS3⟩ := ih u' hfeas hI' hfrac
      refine ⟨S, hones.trans hS1, ?_, hS3⟩
      refine hS2.trans ?_
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      by_cases hit : i = t
      · subst hit; exact ht0
      · rw [hu', Function.update_of_ne hit] at hi; exact hi

end Rounding
end Dev

theorem chk_rounding_step {n d : ℕ} (x : Fin n → Fin d → ℝ) (y : Fin n → ℝ) (e : Fin d → ℝ)
    (θ : ℝ) (hGP : GeneralPosition x) (u : Fin n → ℝ) (hu : u ∈ feasible x y e θ)
    (hI : d ≤ (Finset.univ.filter (fun i => u i = 1)).card) :
    ∃ S : Finset (Fin n), Finset.univ.filter (fun i => u i = 1) ⊆ S ∧
      S ⊆ Finset.univ.filter (fun i => u i ≠ 0) ∧ ind S ∈ feasible x y e θ :=
  Dev.Rounding.step x y e θ hGP _ u hu hI le_rfl

end SampleRemoval

end

theorem solution : type_of% @SampleRemoval.chk_rounding_step := @SampleRemoval.chk_rounding_step
