-- Prove2me | solution 1 for Schanuel.baker_linear_forms_in_logarithms
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-02T08:34:03.776362+00:00
-- url     : https://prove2.me/submissions/1d2c47ee-41e3-4d51-bdc3-59194a307d6e

import Mathlib
import Theorems.Thm_Diaz_exp_ratMul_isAlgebraic
import Theorems.Thm_Transcendence_baker_number_field_basis

/-!
# Baker's theorem, inhomogeneous form (DALAG Th. 1.6), from Th. 4.5

M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups* (2000), §4.2.5: Baker's
Theorem 1.6 as a consequence of Theorem 4.5 (`Transcendence.baker_number_field_basis`).

Suppose `b₀ + Σ_j b_j l_j = 0`. Let `K = ℚ(b_1, …, b_n)`, a number field inside `ℂ`, choose a basis
`(β_i)` of `K` over `ℚ`, and write `b_j = Σ_i c_{ji} β_i` with `c_{ji} ∈ ℚ`. Then
`ℓ'_i = Σ_j c_{ji} l_j` is again a logarithm of an algebraic number (`ℒ` is a `ℚ`-vector space), and
`Σ_i β_i ℓ'_i = Σ_j b_j l_j = -b₀` is algebraic. Theorem 4.5 gives `ℓ' = 0`; the `ℚ`-independence
of the `l_j` gives `c = 0`, hence every `b_j = 0`, and then `b₀ = 0`.

The case where every `b_j` vanishes and `b₀ ≠ 0` needs nothing special: then `K = ℚ` and the
relation itself reads `b₀ = 0`.
-/

open Module

namespace E12_baker_linear_forms_in_logarithms

/-- `e^{Σ q_k ℓ_k}` is algebraic when every `e^{ℓ_k}` is and every `q_k` is rational. -/
theorem isAlgebraic_exp_sum_ratCast_mul {ι : Type*} [Fintype ι] (q : ι → ℚ) (ℓ : ι → ℂ)
    (h : ∀ k, IsAlgebraic ℚ (Complex.exp (ℓ k))) :
    IsAlgebraic ℚ (Complex.exp (∑ k, (q k : ℂ) * ℓ k)) := by
  rw [Complex.exp_sum]
  exact mem_algebraicClosure_iff.1
    (prod_mem fun k _ => mem_algebraicClosure_iff.2 (Diaz.exp_ratMul_isAlgebraic (h k) (q k)))

end E12_baker_linear_forms_in_logarithms

open Module E12_baker_linear_forms_in_logarithms in
theorem solution (n : ℕ) (l : Fin n → ℂ)
    (hl : LinearIndependent ℚ l) (hlalg : ∀ i, IsAlgebraic ℚ (Complex.exp (l i)))
    (b₀ : ℂ) (b : Fin n → ℂ) (hb₀ : IsAlgebraic ℚ b₀) (hb : ∀ i, IsAlgebraic ℚ (b i))
    (hne : b₀ ≠ 0 ∨ ∃ i, b i ≠ 0) :
    b₀ + ∑ i, b i * l i ≠ 0 := by
  intro hrel
  -- `K = ℚ(b_1, …, b_n)` and a basis `β` of `K` over `ℚ`
  let K : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ (Set.range b)
  have : FiniteDimensional ℚ K :=
    IntermediateField.finiteDimensional_adjoin fun x ⟨i, hi⟩ => hi ▸ (hb i).isIntegral
  let β := Module.finBasis ℚ K
  have hmem : ∀ j, b j ∈ K := fun j => IntermediateField.subset_adjoin ℚ _ ⟨j, rfl⟩
  -- `b_j = Σ_i c_{ji} β_i`
  let c : Fin n → Fin (finrank ℚ K) → ℚ := fun j i => β.repr ⟨b j, hmem j⟩ i
  have hbc : ∀ j, b j = ∑ i, (c j i : ℂ) * (β i : ℂ) := by
    intro j
    have h1 := congrArg (fun z : K => (z : ℂ)) (β.sum_repr ⟨b j, hmem j⟩)
    simp only [IntermediateField.coe_sum, Rat.smul_def] at h1
    exact h1.symm
  -- `ℓ'_i = Σ_j c_{ji} l_j ∈ ℒ`
  let ℓ' : Fin (finrank ℚ K) → ℂ := fun i => ∑ j, (c j i : ℂ) * l j
  have hℓ' : ∀ i, IsAlgebraic ℚ (Complex.exp (ℓ' i)) := fun i =>
    isAlgebraic_exp_sum_ratCast_mul (fun j => c j i) l hlalg
  -- `Σ_i β_i ℓ'_i = Σ_j b_j l_j = -b₀`
  have hsum : ∑ i, (β i : ℂ) * ℓ' i = -b₀ := by
    rw [← eq_neg_of_add_eq_zero_right hrel]
    simp only [ℓ', Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hbc j, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  -- Theorem 4.5: `ℓ' = 0`
  have h0 := Transcendence.baker_number_field_basis K β ℓ' hℓ' (by rw [hsum]; exact hb₀.neg)
  -- independence of the `l_j`: `c = 0`, so every `b_j = 0`, and then `b₀ = 0`
  have hc : ∀ j i, c j i = 0 := by
    intro j i
    refine Fintype.linearIndependent_iff.1 hl (fun j => c j i) ?_ j
    simpa [Rat.smul_def] using h0 i
  have hb0 : ∀ j, b j = 0 := by
    intro j
    rw [hbc j]
    simp [hc]
  have hb₀0 : b₀ = 0 := by
    simpa [hb0] using hrel
  rcases hne with h | ⟨i, hi⟩
  · exact h hb₀0
  · exact hi (hb0 i)
