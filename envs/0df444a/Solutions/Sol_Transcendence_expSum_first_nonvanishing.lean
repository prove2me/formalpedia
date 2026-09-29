-- Prove2me | solution 1 for Transcendence.expSum_first_nonvanishing
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:06:06.848832+00:00
-- url     : https://prove2.me/submissions/9c182e6b-cfbd-42a0-9e1e-9dbaab945789

import Mathlib
import Theorems.Thm_FourExp_expPoly_ne_zero

open NumberField

namespace GS_firstnv

/-- The exponential sum `z ↦ ∑ i, c i * exp (ρ i * z)` is analytic at every point. -/
lemma expSum_analyticAt {ι : Type*} [Fintype ι] (c ρ : ι → ℂ) (z : ℂ) :
    AnalyticAt ℂ (fun z : ℂ => ∑ i, c i * Complex.exp (ρ i * z)) z := by
  fun_prop

/-- A nontrivial exponential sum with distinct frequencies is not identically zero: this is
`FourExp.expPoly_ne_zero` with every polynomial of degree `0`, after reindexing `ι` by `Fin`. -/
lemma expSum_ne_zero {ι : Type*} [Fintype ι] (c ρ : ι → ℂ) (hρ : Function.Injective ρ)
    (hc : c ≠ 0) : ∃ w : ℂ, ∑ i, c i * Complex.exp (ρ i * w) ≠ 0 := by
  let e := Fintype.equivFin ι
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hc
  obtain ⟨w, hw⟩ := FourExp.expPoly_ne_zero (fun _ => 1) (ρ ∘ e.symm)
    (hρ.comp e.symm.injective) (fun t _ => c (e.symm t)) ⟨e j, 0, by simpa using hj⟩
  refine ⟨w, fun h => hw ?_⟩
  rw [← e.symm.sum_comp (fun i => c i * Complex.exp (ρ i * w))] at h
  simpa using h

/-- A nontrivial exponential sum has, at every point, some nonvanishing iterated derivative:
otherwise its analytic order there is `⊤`, and the identity theorem makes it vanish on `ℂ`. -/
lemma exists_iteratedDeriv_ne_zero {ι : Type*} [Fintype ι] (c ρ : ι → ℂ)
    (hρ : Function.Injective ρ) (hc : c ≠ 0) (z₀ : ℂ) :
    ∃ k : ℕ, iteratedDeriv k (fun z : ℂ => ∑ i, c i * Complex.exp (ρ i * z)) z₀ ≠ 0 := by
  by_contra! h
  obtain ⟨w, hw⟩ := expSum_ne_zero c ρ hρ hc
  have htop : analyticOrderAt (fun z : ℂ => ∑ i, c i * Complex.exp (ρ i * z)) z₀ = ⊤ :=
    ENat.eq_top_iff_forall_ge.mpr fun n =>
      (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (expSum_analyticAt c ρ z₀)).mpr
        fun i _ => h i
  have hzero := AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (fun z _ => expSum_analyticAt c ρ z) isPreconnected_univ (Set.mem_univ z₀)
    (analyticOrderAt_eq_top.mp htop) (Set.mem_univ w)
  exact hw hzero

end GS_firstnv

-- The first nonvanishing order: `r` is the least `k` such that the `k`-th derivative of the
-- exponential sum is nonzero at some `j ∈ [1, m]`; it exists by `exists_iteratedDeriv_ne_zero`
-- at `j = 1`, and `n ≤ r` because all derivatives of order `< n` vanish there.
open GS_firstnv in
theorem solution {ι : Type*} [Fintype ι] (c ρ : ι → ℂ)
    (hρ : Function.Injective ρ) (hc : c ≠ 0) (m n : ℕ) (hm : 0 < m)
    (hvan : ∀ j : ℕ, 1 ≤ j → j ≤ m → ∀ k < n,
      iteratedDeriv k (fun z : ℂ => ∑ i, c i * Complex.exp (ρ i * z)) (j : ℂ) = 0) :
    ∃ r l₀ : ℕ, n ≤ r ∧ 1 ≤ l₀ ∧ l₀ ≤ m ∧
      iteratedDeriv r (fun z : ℂ => ∑ i, c i * Complex.exp (ρ i * z)) (l₀ : ℂ) ≠ 0 ∧
      ∀ j : ℕ, 1 ≤ j → j ≤ m → ∀ k < r,
        iteratedDeriv k (fun z : ℂ => ∑ i, c i * Complex.exp (ρ i * z)) (j : ℂ) = 0 := by
  classical
  obtain ⟨k₀, hk₀⟩ := exists_iteratedDeriv_ne_zero c ρ hρ hc ((1 : ℕ) : ℂ)
  have hex : ∃ k : ℕ, ∃ l : ℕ, 1 ≤ l ∧ l ≤ m ∧
      iteratedDeriv k (fun z : ℂ => ∑ i, c i * Complex.exp (ρ i * z)) (l : ℂ) ≠ 0 :=
    ⟨k₀, 1, le_rfl, hm, hk₀⟩
  obtain ⟨l₀, h1, h2, hne⟩ := Nat.find_spec hex
  refine ⟨Nat.find hex, l₀, ?_, h1, h2, hne, fun j hj1 hjm k hk => ?_⟩
  · by_contra! hlt
    exact hne (hvan l₀ h1 h2 _ hlt)
  · by_contra hjk
    exact Nat.find_min hex hk ⟨j, hj1, hjm, hjk⟩

#print axioms solution
