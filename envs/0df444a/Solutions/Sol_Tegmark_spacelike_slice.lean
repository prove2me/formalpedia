-- Prove2me | solution 1 for Tegmark.spacelike_slice
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T16:09:05.464988+00:00
-- url     : https://prove2.me/submissions/231fdd89-2c2a-43ec-b73d-0c92b2d52c5b

import Mathlib
import Definitions.Def_Tegmark_sig
import Definitions.Def_Tegmark_phys
import Definitions.Def_Tegmark_ensemble
open Tegmark

theorem g71t_exists_ker {n m : ℕ} (f : World n m →ₗ[ℝ] ℝ) (x y : Fin n ⊕ Fin m) (hxy : x ≠ y) :
    ∃ v : World n m, v ≠ 0 ∧ f v = 0 ∧ ∀ z, z ≠ x → z ≠ y → v z = 0 := by
  by_cases h : f (Pi.single x 1) = 0
  · refine ⟨Pi.single x 1, ?_, h, ?_⟩
    · intro h0; have := congrFun h0 x; simp at this
    · intro z hzx _; simp [Pi.single_apply, hzx]
  · refine ⟨f (Pi.single y 1) • Pi.single x 1 - f (Pi.single x 1) • Pi.single y 1, ?_, ?_, ?_⟩
    · intro h0; have := congrFun h0 y
      simp [Pi.single_apply, hxy.symm] at this; exact h this
    · simp only [map_sub, map_smul, smul_eq_mul]; ring
    · intro z hzx hzy; simp [Pi.single_apply, hzx, hzy]

theorem g71t_teg_nonpos {n m : ℕ} (v : World n m) (h : ∀ i, v (Sum.inl i) = 0) :
    teg n m v ≤ 0 := by
  unfold teg; simp only [h]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    Finset.sum_const_zero, zero_sub, Left.neg_nonpos_iff]
  exact Finset.sum_nonneg (fun j _ => sq_nonneg _)

theorem g71t_teg_nonneg {n m : ℕ} (v : World n m) (h : ∀ j, v (Sum.inr j) = 0) :
    0 ≤ teg n m v := by
  unfold teg; simp only [h]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    Finset.sum_const_zero, sub_zero]
  exact Finset.sum_nonneg (fun j _ => sq_nonneg _)

theorem g71t_no_sp (n m : ℕ) (hm : 2 ≤ m) : ¬ HasSpacelikeHyperplane n m := by
  rintro ⟨f, _, hf⟩
  obtain ⟨v, hv0, hfv, hz⟩ := g71t_exists_ker f (Sum.inr ⟨0, by omega⟩) (Sum.inr ⟨1, by omega⟩)
    (by simp)
  have := hf v (LinearMap.mem_ker.mpr hfv) hv0
  have := g71t_teg_nonpos v (fun i => hz _ (by simp) (by simp))
  linarith

theorem g71t_no_tl (n m : ℕ) (hn : 2 ≤ n) : ¬ HasTimelikeHyperplane n m := by
  rintro ⟨f, _, hf⟩
  obtain ⟨v, hv0, hfv, hz⟩ := g71t_exists_ker f (Sum.inl ⟨0, by omega⟩) (Sum.inl ⟨1, by omega⟩)
    (by simp)
  have := hf v (LinearMap.mem_ker.mpr hfv) hv0
  have := g71t_teg_nonneg v (fun i => hz _ (by simp) (by simp))
  linarith

theorem g71t_slice (n : ℕ) : HasSpacelikeHyperplane n 1 := by
  refine ⟨LinearMap.proj (Sum.inr 0), ?_, ?_⟩
  · intro h; have := LinearMap.congr_fun h (Pi.single (Sum.inr 0) 1); simp at this
  · intro v hv hv0
    rw [LinearMap.mem_ker, LinearMap.proj_apply] at hv
    obtain ⟨x, hx⟩ : ∃ x, v x ≠ 0 := by
      by_contra hc; push_neg at hc; exact hv0 (funext hc)
    rcases x with i | j
    · unfold teg
      have hj : ∀ j : Fin 1, v (Sum.inr j) = 0 := fun j => by rw [Subsingleton.elim j 0]; exact hv
      simp only [hj, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        Finset.sum_const_zero, sub_zero]
      exact lt_of_lt_of_le (by positivity) (Finset.single_le_sum (f := fun i => v (Sum.inl i) ^ 2)
        (fun k _ => sq_nonneg _) (Finset.mem_univ i))
    · exact absurd (by rw [Subsingleton.elim j 0]; exact hv) hx

theorem solution (n : ℕ) : HasSpacelikeHyperplane n 1 := g71t_slice n
