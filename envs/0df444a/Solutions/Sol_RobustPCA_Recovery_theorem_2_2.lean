-- Prove2me | solution 1 for RobustPCA.Recovery.theorem_2_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:16:06.570222+00:00
-- url     : https://prove2.me/submissions/0880a070-7493-478f-ae55-851661d62609

import Definitions.Def_RobustPCA_Recovery_Setup
open MatrixCompletion

namespace Aux_RobustPCA_theorem_2_2
open RobustPCA.Recovery

theorem l1_add_le {n : ℕ} (A B : RealMatrix n n) : l1Norm (A + B) ≤ l1Norm A + l1Norm B := by
  unfold l1Norm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [Matrix.add_apply]
  exact abs_add_le _ _

theorem l1_split {n : ℕ} (S0 S0' : RealMatrix n n) (htrim : IsTrimmed S0' S0) :
    l1Norm S0 = l1Norm S0' + l1Norm (S0 - S0') := by
  unfold l1Norm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.sub_apply]
  by_cases h : S0' i j = 0
  · rw [h, sub_zero, abs_zero, zero_add]
  · rw [htrim.2 i j h, sub_self, abs_zero, add_zero]

end Aux_RobustPCA_theorem_2_2

open RobustPCA.Recovery in
theorem solution {n : ℕ} (lam : ℝ) (L0 S0 S0' : RealMatrix n n) (hlam : 0 ≤ lam)
    (hexact : IsPCPExact lam L0 S0) (htrim : IsTrimmed S0' S0) :
    IsPCPExact lam L0 S0' := by
  intro L S h hne
  have hsum : L + (S + (S0 - S0')) = L0 + S0 := by
    rw [← add_assoc, h]
    abel
  have hne' : (L, S + (S0 - S0')) ≠ (L0, S0) := by
    intro heq
    apply hne
    have h1 : L = L0 := congrArg Prod.fst heq
    have h2 : S + (S0 - S0') = S0 := congrArg Prod.snd heq
    have h3 : S = S0 - (S0 - S0') := eq_sub_of_add_eq h2
    rw [h1, h3, sub_sub_cancel]
  have key := hexact L (S + (S0 - S0')) hsum hne'
  have tri := Aux_RobustPCA_theorem_2_2.l1_add_le S (S0 - S0')
  have spl := Aux_RobustPCA_theorem_2_2.l1_split S0 S0' htrim
  have := mul_le_mul_of_nonneg_left tri hlam
  rw [spl] at key
  nlinarith
