-- Prove2me | solution 1 for RandomGradFree.Accelerated.c_bound_strongly_convex
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T11:19:20.097674+00:00
-- url     : https://prove2.me/submissions/14f1f1ca-bc8f-4c7b-914d-6eebcc132c3d

import Definitions.Def_RandomGradFree_Accelerated_C
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Tactic
open RandomGradFree.Accelerated
open scoped BigOperators

theorem solution (n : ℕ) (α : ℕ → ℝ) (hα : ∀ j, 0 ≤ α j ∧ α j ≤ 1)
    (τ : ℝ) (hτ : 0 < τ) (L₁ : ℝ) (hL₁ : 0 < L₁)
    (hακ : ∀ j, Real.sqrt (τ / L₁) / (4 * ((n : ℝ) + 4)) ≤ α j)
    (k : ℕ) : C α k ≤ 4 * ((n : ℝ) + 4) / Real.sqrt (τ / L₁) := by
  let a:=Real.sqrt (τ/L₁)/(4*((n:ℝ)+4))
  let q:=1-a
  let K:=4*((n:ℝ)+4)/Real.sqrt (τ/L₁)
  have hsqrt:0 < Real.sqrt (τ/L₁):=Real.sqrt_pos.2 (div_pos hτ hL₁)
  have hden:0 < 4*((n:ℝ)+4):=by positivity
  have ha:0 < a:=div_pos hsqrt hden
  have ha1:a ≤ 1:=(hακ 0).trans (hα 0).2
  have hq:0 ≤ q:=sub_nonneg.mpr ha1
  have hK:0 < K:=div_pos hden hsqrt
  have hKa:a*K=1:=by dsimp [a,K];field_simp
  have hsum:(∑ i∈Finset.range k,q^i) ≤ K := by
    have he:=geom_sum_mul q k
    have he' : a*(∑ i∈Finset.range k,q^i)=1-q^k := by dsimp [q] at *;nlinarith
    have hp:=pow_nonneg hq k
    nlinarith
  by_cases hk:k=0
  · subst k;simpa [C] using hK.le
  · have hprod (i : ℕ) (hi : i∈Finset.Ico 1 k) :
        (∏ j∈Finset.Ico (k-i) k,(1-α j)) ≤ q^i := by
      have hh:=Finset.prod_le_prod (fun j (_ : j∈Finset.Ico (k-i) k)=>sub_nonneg.mpr (hα j).2)
        (fun j (_ : j∈Finset.Ico (k-i) k)=>show 1-α j ≤ q from sub_le_sub_left (hακ j) 1)
      have hic:i ≤ k:=by have := (Finset.mem_Ico.mp hi).2;omega
      simpa [Finset.prod_const,Nat.card_Ico,Nat.sub_sub_self hic] using hh
    have hh:=Finset.sum_le_sum hprod
    have he:1+(∑ i∈Finset.Ico 1 k,q^i)=∑ i∈Finset.range k,q^i := by
      rw [Finset.sum_Ico_eq_sub (fun i=>q^i) (by omega : 1 ≤ k)]
      simp
    rw [C,if_neg hk]
    calc
      _ ≤ 1+∑ i∈Finset.Ico 1 k,q^i:=by linarith
      _ = ∑ i∈Finset.range k,q^i:=he
      _ ≤ K:=hsum
