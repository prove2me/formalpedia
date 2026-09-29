-- Prove2me | solution 1 for SetCoverThreshold.MaxCover.cube_cover_count
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:13:30.473507+00:00
-- url     : https://prove2.me/submissions/6f10954c-1be6-4c7a-9ab2-c4835b5adcdb

import Mathlib
import Definitions.Def_SetCoverThreshold_MaxCover_Reduction

namespace SetCoverThreshold.MaxCover

theorem aux_ccc_compl_card (k : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (J : Finset ι) (v : ι → Fin k) :
    (Finset.univ.filter (fun x : ι → Fin k => ¬ ∃ i ∈ J, cubeSystem k ι x i = v i)).card =
      ∏ i, (if i ∈ J then k - 1 else k) := by
  have hT : (Finset.univ.filter (fun x : ι → Fin k => ¬ ∃ i ∈ J, cubeSystem k ι x i = v i)) =
      Fintype.piFinset (fun i => if i ∈ J then Finset.univ.erase (v i) else Finset.univ) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, cubeSystem,
      not_exists, not_and]
    constructor
    · intro h i
      split_ifs with hi
      · simp [h i hi]
      · simp
    · intro h i hi hx
      have := h i
      rw [if_pos hi] at this
      simp [hx] at this
  rw [hT, Fintype.card_piFinset]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  split_ifs with hi
  · simp [Finset.card_erase_of_mem]
  · simp

end SetCoverThreshold.MaxCover

open SetCoverThreshold.MaxCover

theorem solution (k : ℕ) (hk : 1 ≤ k) (ι : Type) [Fintype ι] [DecidableEq ι]
    (J : Finset ι) (v : ι → Fin k) :
    ((Finset.univ.filter (fun x : ι → Fin k => ∃ i ∈ J, cubeSystem k ι x i = v i)).card : ℝ) =
      (1 - (1 - 1 / (k : ℝ)) ^ J.card) * (k : ℝ) ^ Fintype.card ι := by
  have hk' : (k : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hc := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (ι → Fin k)))
    (fun x : ι → Fin k => ∃ i ∈ J, cubeSystem k ι x i = v i)
  rw [aux_ccc_compl_card, Finset.card_univ, Fintype.card_fun, Fintype.card_fin] at hc
  have hcR : ((Finset.univ.filter (fun x : ι → Fin k => ∃ i ∈ J, cubeSystem k ι x i = v i)).card : ℝ)
      + ∏ i, (if i ∈ J then (k : ℝ) - 1 else k) = (k : ℝ) ^ Fintype.card ι := by
    have := congrArg (fun n : ℕ => (n : ℝ)) hc
    simp only [Nat.cast_add, Nat.cast_prod, Nat.cast_pow] at this
    rw [← this]
    congr 1
    refine Finset.prod_congr rfl (fun i _ => ?_)
    split_ifs
    · rw [Nat.cast_sub hk]; simp
    · rfl
  have hprod : ∏ i, (if i ∈ J then (k : ℝ) - 1 else k) =
      (1 - 1 / (k : ℝ)) ^ J.card * (k : ℝ) ^ Fintype.card ι := by
    have : ∀ i, (if i ∈ J then (k : ℝ) - 1 else k) =
        (if i ∈ J then (1 - 1 / (k : ℝ)) else 1) * k := by
      intro i
      split_ifs
      · field_simp
      · ring
    rw [Finset.prod_congr rfl (fun i _ => this i), Finset.prod_mul_distrib, Finset.prod_ite_mem,
      Finset.univ_inter, Finset.prod_const, Finset.prod_const, Finset.card_univ]
  rw [hprod] at hcR
  linarith
