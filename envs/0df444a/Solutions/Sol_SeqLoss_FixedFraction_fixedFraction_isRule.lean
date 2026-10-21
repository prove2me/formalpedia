-- Prove2me | solution 1 for SeqLoss.FixedFraction.fixedFraction_isRule
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:03:37.150344+00:00
-- url     : https://prove2.me/submissions/1f134ea9-7325-428e-964e-28d75619fe46

import Mathlib
import Definitions.Def_SeqLoss_FixedFraction_Setting
import Definitions.Def_SeqLoss_FixedFraction_Axioms

set_option autoImplicit false
open SeqLoss.FixedFraction

theorem solution (lam : ℝ) (hlam : lam ∈ Set.Icc (0:ℝ) 1) :
    IsRule (fixedFraction lam) := by
  obtain ⟨h0, h1⟩ := hlam
  intro n ℓ hℓ
  have hL : 0 ≤ ∑ j, ℓ j := Finset.sum_nonneg (fun j _ => hℓ j)
  have hite : ∀ (T : Finset (Fin n)) (c : ℝ) (i0 : Fin n), i0.val = 0 → i0 ∈ T →
      ∑ i ∈ T, (if i.val = 0 then c else 0) = c := by
    intro T c i0 h0 hT
    rw [Finset.sum_eq_single i0]
    · simp [h0]
    · intro j _ hj
      have : j.val ≠ 0 := fun hh => hj (Fin.ext (by omega))
      simp [this]
    · intro hn; exact absurd hT hn
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro i
    unfold fixedFraction
    have := hℓ i
    have : 0 ≤ (if i.val = 0 then (1 - lam) * ∑ j, ℓ j else 0) := by
      split_ifs
      · exact mul_nonneg (by linarith) hL
      · exact le_rfl
    nlinarith
  · intro m hm
    have hn : 0 < n := by omega
    set T : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => i.val ≤ m) with hT
    have hmem : (⟨0, hn⟩ : Fin n) ∈ T := by simp [hT]
    have hsub : ∑ i ∈ T, ℓ i ≤ ∑ j, ℓ j :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => hℓ j)
    unfold fixedFraction
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hite T _ ⟨0, hn⟩ rfl hmem]
    nlinarith
  · unfold fixedFraction
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · rw [Finset.sum_add_distrib, ← Finset.mul_sum, hite Finset.univ _ ⟨0, hn⟩ rfl (Finset.mem_univ _)]
      ring
  · have hc : Continuous (fun a : ℝ => fixedFraction lam n (a • ℓ)) := by
      apply continuous_pi
      intro i
      unfold fixedFraction
      by_cases hi : i.val = 0
      · simp only [hi, if_true, Pi.smul_apply, smul_eq_mul]
        fun_prop
      · simp only [hi, if_false, Pi.smul_apply, smul_eq_mul]
        fun_prop
    have := hc.tendsto 1
    simpa using this
