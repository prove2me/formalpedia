-- Prove2me | solution 1 for ShiShallow.mul_comm_of_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-10T04:57:12.866798+00:00
-- url     : https://prove2.me/submissions/f3ed9702-34d3-4929-965e-6a0e7b663cd0

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

section
open ShiShallow

theorem solution {n : ℕ} {G T : Finset (Fin n)} {A V : Op n}
    (hA : IsLocal T A) (hV : IsLocal G V) (hd : Disjoint G T) : A * V = V * A := by
  classical
  have hGT : ∀ k, k ∈ G → k ∉ T := fun k hk => Finset.disjoint_left.1 hd hk
  have hTG : ∀ k, k ∈ T → k ∉ G := fun k hk hc => hGT k hc hk
  ext y z
  set u₀ : Bits n := fun k => if k ∈ T then z k else y k with hu₀def
  set u₁ : Bits n := fun k => if k ∈ G then z k else y k with hu₁def
  have hu₀T : ∀ k, k ∈ T → u₀ k = z k := by
    intro k hk; simp only [hu₀def]; exact if_pos hk
  have hu₀nT : ∀ k, k ∉ T → u₀ k = y k := by
    intro k hk; simp only [hu₀def]; exact if_neg hk
  have hu₁G : ∀ k, k ∈ G → u₁ k = z k := by
    intro k hk; simp only [hu₁def]; exact if_pos hk
  have hu₁nG : ∀ k, k ∉ G → u₁ k = y k := by
    intro k hk; simp only [hu₁def]; exact if_neg hk
  have e1 : (A * V) y z = A y u₀ * V u₀ z := by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_single u₀ (fun u _ hu => ?_) (fun h => absurd (Finset.mem_univ _) h)
    by_cases h1 : ∀ k, k ∉ T → y k = u k
    · by_cases h2 : ∀ k, k ∉ G → u k = z k
      · refine absurd (funext fun k => ?_) hu
        by_cases hk : k ∈ T
        · rw [hu₀T k hk]; exact h2 k (hTG k hk)
        · rw [hu₀nT k hk]; exact (h1 k hk).symm
      · rw [hV.vanish h2, mul_zero]
    · rw [hA.vanish h1, zero_mul]
  have e2 : (V * A) y z = V y u₁ * A u₁ z := by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_single u₁ (fun u _ hu => ?_) (fun h => absurd (Finset.mem_univ _) h)
    by_cases h1 : ∀ k, k ∉ G → y k = u k
    · by_cases h2 : ∀ k, k ∉ T → u k = z k
      · refine absurd (funext fun k => ?_) hu
        by_cases hk : k ∈ G
        · rw [hu₁G k hk]; exact h2 k (hGT k hk)
        · rw [hu₁nG k hk]; exact (h1 k hk).symm
      · rw [hA.vanish h2, mul_zero]
    · rw [hV.vanish h1, zero_mul]
  rw [e1, e2]
  by_cases hrest : ∀ k, k ∉ G ∪ T → y k = z k
  · have hAeq : A y u₀ = A u₁ z := by
      refine hA.entry_congr (fun k hk => (hu₁nG k (hTG k hk)).symm) (fun k hk => hu₀T k hk)
        (fun k hk => (hu₀nT k hk).symm) (fun k hk => ?_)
      by_cases hkG : k ∈ G
      · exact hu₁G k hkG
      · rw [hu₁nG k hkG]
        refine hrest k (fun hc => ?_)
        rcases Finset.mem_union.1 hc with h | h
        · exact hkG h
        · exact hk h
    have hVeq : V u₀ z = V y u₁ := by
      refine hV.entry_congr (fun k hk => hu₀nT k (hGT k hk)) (fun k hk => (hu₁G k hk).symm)
        (fun k hk => ?_) (fun k hk => (hu₁nG k hk).symm)
      by_cases hkT : k ∈ T
      · exact hu₀T k hkT
      · rw [hu₀nT k hkT]
        refine hrest k (fun hc => ?_)
        rcases Finset.mem_union.1 hc with h | h
        · exact hk h
        · exact hkT h
    rw [hAeq, hVeq]
    ring
  · push_neg at hrest
    obtain ⟨k₀, hk₀, hne⟩ := hrest
    have hk₀G : k₀ ∉ G := fun h => hk₀ (Finset.mem_union_left _ h)
    have hk₀T : k₀ ∉ T := fun h => hk₀ (Finset.mem_union_right _ h)
    rw [hV.vanish (fun hc => hne ((hu₀nT k₀ hk₀T).symm.trans (hc k₀ hk₀G))),
      hA.vanish (fun hc => hne ((hu₁nG k₀ hk₀G).symm.trans (hc k₀ hk₀T)))]
    ring

end
