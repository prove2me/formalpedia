-- Prove2me | solution 1 for RossSolandGAP.Bound.agent_subproblem_value
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T09:10:52.73835+00:00
-- url     : https://prove2.me/submissions/4ddffdfd-c7c2-42e2-920f-d0db8bf89f6f

import Definitions.Def_RossSolandGAP_Bound_Model
import Mathlib.Tactic
set_option autoImplicit false
open Finset RossSolandGAP.Bound

private theorem penalty_eq {m n : ℕ} (hm : 1 < m) (c : Fin m → Fin n → ℝ)
    (a : Fin n → Fin m) (j : Fin n) : pen hm c a j = c2 hm c a j-c (a j) j := by
  obtain ⟨k,hk,hmin⟩ := Finset.exists_mem_eq_inf' (others_nonempty hm (a j)) (fun k => c k j)
  apply le_antisymm
  · have hh := Finset.inf'_le (fun k => c k j-c (a j) j) hk
    change pen hm c a j ≤ c k j-c (a j) j at hh
    simpa only [c2,hmin] using hh
  · apply Finset.le_inf'
    intro k hk
    exact sub_le_sub_right (Finset.inf'_le (fun k => c k j) hk) _

private theorem sum_restrict {m n : ℕ} (a : Fin n → Fin m) (i : Fin m) (v f : Fin n → ℝ)
    (hv : ∀ j, a j ≠ i → v j=0) : ∑ j, f j*v j = ∑ j ∈ Jset a i, f j*v j := by
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro j hj hnot
  have hn : a j ≠ i := by simpa [Jset] using hnot
  simp [hv j hn]

private theorem substitution {m n : ℕ} (hm : 1 < m) (c r : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (a : Fin n → Fin m) (ha : IsCheapest c a) (i : Fin m) (v : Fin n → ℝ)
    (hv : ∀ j, a j ≠ i → v j = 0) :
    (∀ j, pen hm c a j = c2 hm c a j - c (a j) j) ∧
    ∑ j, (c i j - c2 hm c a j) * v j =
      -(∑ j ∈ Jset a i, pen hm c a j) + ∑ j ∈ Jset a i, pen hm c a j * (1 - v j) ∧
    (∑ j, r i j * v j ≤ b i ↔ dgap r b a i ≤ ∑ j ∈ Jset a i, r i j * (1 - v j)) := by
  refine ⟨penalty_eq hm c a,?_,?_⟩
  · rw [sum_restrict a i v (fun j => c i j-c2 hm c a j) hv]
    rw [← Finset.sum_neg_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have he : a j=i := by simpa [Jset] using hj
    rw [penalty_eq,he]
    ring
  · rw [sum_restrict a i v (r i) hv]
    have hs : ∑ j ∈ Jset a i, r i j*(1-v j) = load r a i-∑ j ∈ Jset a i, r i j*v j := by
      simp only [mul_sub,mul_one,Finset.sum_sub_distrib,load]
    rw [hs,dgap]
    constructor <;> intro h <;> linarith

private theorem penalty_nonneg {m n : ℕ} (hm : 1 < m) (c : Fin m → Fin n → ℝ)
    (a : Fin n → Fin m) (ha : IsCheapest c a) (j : Fin n) : 0 ≤ pen hm c a j := by
  apply Finset.le_inf'
  intro k hk
  exact sub_nonneg.mpr (ha j k)

private theorem pk_min {m n : ℕ} (hm : 1 < m) (c r : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (a : Fin n → Fin m) (ha : IsCheapest c a) (i : Fin m)
    (y : Fin n → ℝ) (hy : IsOptPK hm c r b a i y) :
      (∀ v, KnapFeasible r b i v → (∀ j, a j ≠ i → v j = 0) →
        -(∑ j ∈ Jset a i, pen hm c a j) + pkObj hm c a i y ≤
          ∑ j, (c i j - c2 hm c a j) * v j) ∧
      ∃ v, KnapFeasible r b i v ∧ (∀ j, a j ≠ i → v j = 0) ∧
        ∑ j, (c i j - c2 hm c a j) * v j =
          -(∑ j ∈ Jset a i, pen hm c a j) + pkObj hm c a i y := by
  constructor
  · intro v hv hs
    have hsub := substitution hm c r b a ha i v hs
    have hpk : FeasiblePK r b a i (fun j => 1-v j) := by
      constructor
      · intro j hj
        rcases hv.1 j with h|h <;> simp [h]
      · exact hsub.2.2.mp hv.2
    rw [hsub.2.1]
    exact add_le_add_right (hy.2 _ hpk) _
  · let v : Fin n → ℝ := fun j => if a j=i then 1-y j else 0
    have hs : ∀ j, a j≠i → v j=0 := by intro j hj; simp [v,hj]
    have hsub := substitution hm c r b a ha i v hs
    have he (j : Fin n) (hj : j∈Jset a i) : 1-v j=y j := by
      have hh : a j=i := by simpa [Jset] using hj
      simp [v,hh]
    refine ⟨v,⟨?_,?_⟩,hs,?_⟩
    · intro j
      by_cases hj : a j=i
      · have hmem : j∈Jset a i := by simp [Jset,hj]
        rcases hy.1.1 j hmem with h|h <;> simp [v,hj,h]
      · simp [v,hj]
    · apply hsub.2.2.mpr
      have heq : ∑ j ∈ Jset a i, r i j*(1-v j) = ∑ j ∈ Jset a i, r i j*y j := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [he j hj]
      rw [heq]
      exact hy.1.2
    · rw [hsub.2.1]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [he j hj]

theorem solution {m n : ℕ} (hm : 1 < m) (c r : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (a : Fin n → Fin m) (ha : IsCheapest c a) (i : Fin m) :
    (i ∈ Iprime r b a → ∀ y, IsOptPK hm c r b a i y →
      (∀ v, KnapFeasible r b i v → (∀ j, a j ≠ i → v j = 0) →
        -(∑ j ∈ Jset a i, pen hm c a j) + pkObj hm c a i y ≤
          ∑ j, (c i j - c2 hm c a j) * v j) ∧
      ∃ v, KnapFeasible r b i v ∧ (∀ j, a j ≠ i → v j = 0) ∧
        ∑ j, (c i j - c2 hm c a j) * v j =
          -(∑ j ∈ Jset a i, pen hm c a j) + pkObj hm c a i y) ∧
    (i ∉ Iprime r b a →
      (∀ v, KnapFeasible r b i v → (∀ j, a j ≠ i → v j = 0) →
        -(∑ j ∈ Jset a i, pen hm c a j) ≤ ∑ j, (c i j - c2 hm c a j) * v j) ∧
      ∃ v, KnapFeasible r b i v ∧ (∀ j, a j ≠ i → v j = 0) ∧
        ∑ j, (c i j - c2 hm c a j) * v j = -(∑ j ∈ Jset a i, pen hm c a j)) := by
  constructor
  · intro hi y hy
    exact pk_min hm c r b a ha i y hy
  · intro hi
    have hlo : load r a i ≤ b i := by simpa [Iprime] using hi
    have hy : IsOptPK hm c r b a i (fun _ => 0) := by
      constructor
      · constructor
        · intro j hj; exact Or.inl rfl
        · simp only [mul_zero,Finset.sum_const_zero,dgap]
          linarith
      · intro y hy
        simp only [pkObj,mul_zero,Finset.sum_const_zero]
        apply Finset.sum_nonneg
        intro j hj
        have hy0 : 0 ≤ y j := by rcases hy.1 j hj with h|h <;> simp [h]
        exact mul_nonneg (penalty_nonneg hm c a ha j) hy0
    simpa [pkObj] using pk_min hm c r b a ha i (fun _ => 0) hy
