-- Prove2me | solution 1 for SelfCorrect3D.Memory.peierls_contains_coboundary
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T04:49:19.791755+00:00
-- url     : https://prove2.me/submissions/4cbafa9e-30f7-4908-bf34-fbc34c0a061e

import Mathlib

namespace Aux_Peierls

theorem H1 : ∀ a b : ZMod 2, (b ≠ 0 → a ≠ 0) → (a ≠ 0 ↔ b ≠ 0 ∨ a + b ≠ 0) := by decide

theorem H2 : ∀ a b : ZMod 2, (b ≠ 0 → a ≠ 0) → b ≠ 0 → a + b = 0 := by decide

theorem hcard {m : ℕ} (σ τ : Fin m → ZMod 2) (h : ∀ i, τ i ≠ 0 → σ i ≠ 0) :
    hammingNorm σ = hammingNorm τ + hammingNorm (σ + τ) := by
  classical
  unfold hammingNorm
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext i
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, Pi.add_apply]
    exact H1 _ _ (h i)
  · rw [Finset.disjoint_filter]
    intro i _ hi
    simp only [Pi.add_apply, ne_eq, not_not]
    exact H2 _ _ (h i) hi

end Aux_Peierls

open Classical in
theorem solution {n m : ℕ}
    (δ : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2)) (τ : Fin m → ZMod 2)
    (hτ : τ ∈ LinearMap.range δ) (β : ℝ) :
    (∑ σ ∈ Finset.univ.filter (fun σ : Fin m → ZMod 2 =>
          σ ∈ LinearMap.range δ ∧ ∀ i, τ i ≠ 0 → σ i ≠ 0),
        Real.exp (-β * hammingNorm σ)) /
      (∑ σ ∈ Finset.univ.filter (fun σ : Fin m → ZMod 2 => σ ∈ LinearMap.range δ),
        Real.exp (-β * hammingNorm σ)) ≤
      Real.exp (-β * hammingNorm τ) := by
  set Aset := Finset.univ.filter (fun σ : Fin m → ZMod 2 =>
          σ ∈ LinearMap.range δ ∧ ∀ i, τ i ≠ 0 → σ i ≠ 0) with hA
  set Rset := Finset.univ.filter (fun σ : Fin m → ZMod 2 => σ ∈ LinearMap.range δ) with hR
  have hden : 0 < ∑ σ ∈ Rset, Real.exp (-β * hammingNorm σ) := by
    apply Finset.sum_pos (fun _ _ => Real.exp_pos _)
    exact ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Submodule.zero_mem _⟩⟩
  rw [div_le_iff₀ hden]
  have step1 : ∑ σ ∈ Aset, Real.exp (-β * hammingNorm σ) =
      Real.exp (-β * hammingNorm τ) * ∑ σ ∈ Aset, Real.exp (-β * hammingNorm (σ + τ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ hσ => ?_
    have hσ' := (Finset.mem_filter.mp hσ).2.2
    rw [Aux_Peierls.hcard σ τ hσ', Nat.cast_add, mul_add, Real.exp_add]
  have step2 : ∑ σ ∈ Aset, Real.exp (-β * hammingNorm (σ + τ)) ≤
      ∑ σ ∈ Rset, Real.exp (-β * hammingNorm σ) := by
    have hinj : Set.InjOn (fun σ : Fin m → ZMod 2 => σ + τ) Aset := fun a _ b _ h =>
      add_right_cancel h
    rw [← Finset.sum_image (f := fun σ => Real.exp (-β * hammingNorm σ)) hinj]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro x hx
      obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hx
      have hσR := (Finset.mem_filter.mp hσ).2.1
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Submodule.add_mem _ hσR hτ⟩
    · intro _ _ _; exact (Real.exp_pos _).le
  rw [step1]
  exact mul_le_mul_of_nonneg_left step2 (Real.exp_pos _).le
