-- Prove2me | solution 1 for ShiShallow.IsLocal.mul
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-10T05:36:45.530882+00:00
-- url     : https://prove2.me/submissions/7359db79-45c9-46c0-8ab8-ea48dfcb5bdf

/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi

Shallow quantum circuits and causal cones.

MODIFICATIONS made for publication on Prove2me: the enclosing `namespace` is replaced by `section`+`open` and the target theorem is renamed to `solution`;
no statement or proof was otherwise altered.

Built against Mathlib (Apache-2.0) at revision 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Definitions.Def_ShiShallow_Circuit
import Definitions.Def_ShiShallow_Operator
import Theorems.Thm_ShiShallow_sum_of_vanishing

section
open ShiShallow

theorem solution {n : ℕ} {S₁ S₂ : Finset (Fin n)} {X Y : Op n}
    (hX : IsLocal S₁ X) (hY : IsLocal S₂ Y) : IsLocal (S₁ ∪ S₂) (X * Y) := by
  classical
  have hsub1 : S₁ ⊆ S₁ ∪ S₂ := Finset.subset_union_left
  have hsub2 : S₂ ⊆ S₁ ∪ S₂ := Finset.subset_union_right
  constructor
  · intro y z hne
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun u _ => ?_
    by_cases h1 : ∀ k, k ∉ S₁ → y k = u k
    · by_cases h2 : ∀ k, k ∉ S₂ → u k = z k
      · exact absurd (fun k hk => (h1 k (fun hc => hk (Finset.mem_union_left _ hc))).trans
          (h2 k (fun hc => hk (Finset.mem_union_right _ hc)))) hne
      · rw [hY.vanish h2, mul_zero]
    · rw [hX.vanish h1, zero_mul]
  · intro y z y' z' hy hz hyz hyz'
    have hcol : ∀ a b : Bits n, (X * Y) a b
        = ∑ w : {k : Fin n // k ∈ S₁} → Bool,
            X a (graft S₁ a w) * Y (graft S₁ a w) b := by
      intro a b
      rw [Matrix.mul_apply]
      refine sum_of_vanishing S₁ a (fun u => X a u * Y u b) ?_
      intro u hu
      rw [hX.vanish (fun hc => hu (fun k hk => (hc k hk).symm)), zero_mul]
    rw [hcol y z, hcol y' z']
    refine Finset.sum_congr rfl fun w _ => ?_
    have hXeq : X y (graft S₁ y w) = X y' (graft S₁ y' w) := by
      refine hX.entry_congr (fun k hk => hy k (hsub1 hk)) (fun k hk => ?_)
        (fun k hk => (graft_of_not_mem S₁ y w hk).symm)
        (fun k hk => (graft_of_not_mem S₁ y' w hk).symm)
      rw [graft_of_mem S₁ y w hk, graft_of_mem S₁ y' w hk]
    have hout : ∀ k, k ∉ S₁ → k ∉ S₂ → k ∉ S₁ ∪ S₂ := by
      intro k h1 h2 hc
      rcases Finset.mem_union.1 hc with h | h
      · exact h1 h
      · exact h2 h
    by_cases hP : ∀ k, k ∉ S₂ → graft S₁ y w k = z k
    · have hP' : ∀ k, k ∉ S₂ → graft S₁ y' w k = z' k := by
        intro k hk
        by_cases hk1 : k ∈ S₁
        · rw [graft_of_mem S₁ y' w hk1]
          have hw := hP k hk
          rw [graft_of_mem S₁ y w hk1] at hw
          rw [hw]
          exact hz k (hsub1 hk1)
        · rw [graft_of_not_mem S₁ y' w hk1]
          exact hyz' k (hout k hk1 hk)
      have hYeq : Y (graft S₁ y w) z = Y (graft S₁ y' w) z' := by
        refine hY.entry_congr (fun k hk => ?_) (fun k hk => hz k (hsub2 hk)) hP hP'
        by_cases hk1 : k ∈ S₁
        · rw [graft_of_mem S₁ y w hk1, graft_of_mem S₁ y' w hk1]
        · rw [graft_of_not_mem S₁ y w hk1, graft_of_not_mem S₁ y' w hk1]
          exact hy k (hsub2 hk)
      rw [hXeq, hYeq]
    · have hP'' : ¬ ∀ k, k ∉ S₂ → graft S₁ y' w k = z' k := by
        intro hQ
        refine hP fun k hk => ?_
        by_cases hk1 : k ∈ S₁
        · rw [graft_of_mem S₁ y w hk1]
          have hw := hQ k hk
          rw [graft_of_mem S₁ y' w hk1] at hw
          rw [hw]
          exact (hz k (hsub1 hk1)).symm
        · rw [graft_of_not_mem S₁ y w hk1]
          exact hyz k (hout k hk1 hk)
      rw [hY.vanish hP, hY.vanish hP'', mul_zero, mul_zero]

end
