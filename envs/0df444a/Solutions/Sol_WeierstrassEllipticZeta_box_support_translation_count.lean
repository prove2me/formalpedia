-- Prove2me | solution 1 for WeierstrassEllipticZeta.box_support_translation_count
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-13T04:23:40.189248+00:00
-- url     : https://prove2.me/submissions/61b14ef6-6b2e-4b4a-a178-b081a7c0f76e

import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Data.Finsupp.Interval
import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Finset.Nat

open scoped Classical

noncomputable section

theorem solution
    (K σ : Type*) [CommSemiring K] [Fintype σ] [DecidableEq σ]
    (p : MvPolynomial σ K) (hp : p ≠ 0) (b : σ →₀ ℕ)
    (hfit : ∀ i : σ, p.degreeOf i ≤ b i) :
    let E : Set (σ →₀ ℕ) := {d | ∀ e ∈ p.support, e + d ∈ Finset.Iic b}
    E.Finite ∧
      (∀ d : σ →₀ ℕ, d ∈ E ↔ ∀ i : σ, d i ≤ b i - p.degreeOf i) ∧
      E.ncard = ∏ i : σ, (b i - p.degreeOf i + 1) ∧
      (Finset.Iic b).card = ∏ i : σ, (b i + 1) := by
  classical
  let E : Set (σ →₀ ℕ) := {d | ∀ e ∈ p.support, e + d ∈ Finset.Iic b}
  let r : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun i => b i - p.degreeOf i)
  have hmem (d : σ →₀ ℕ) : d ∈ E ↔ d ≤ r := by
    constructor
    · intro hd i
      obtain ⟨e, he, hmax⟩ :=
        Finset.exists_mem_eq_sup p.support (MvPolynomial.support_nonempty.mpr hp)
          (fun e => e i)
      have hdegree : p.degreeOf i = e i := by
        rw [MvPolynomial.degreeOf_eq_sup, hmax]
      have hbound : e i + d i ≤ b i := (Finset.mem_Iic.mp (hd e he)) i
      change d i ≤ b i - p.degreeOf i
      omega
    · intro hd e he
      apply Finset.mem_Iic.mpr
      intro i
      have hdi : d i ≤ b i - p.degreeOf i := hd i
      have hei : e i ≤ p.degreeOf i := MvPolynomial.monomial_le_degreeOf i he
      have hbi := hfit i
      change e i + d i ≤ b i
      omega
  have hE : E = (Finset.Iic r : Set (σ →₀ ℕ)) := by
    ext d
    exact (hmem d).trans Finset.mem_Iic.symm
  have hcard (v : σ →₀ ℕ) : (Finset.Iic v).card = ∏ i : σ, (v i + 1) := by
    rw [Finsupp.card_Iic]
    simp only [Nat.card_Iic]
    apply Finset.prod_subset (Finset.subset_univ _)
    intro i _ hi
    rw [Finsupp.notMem_support_iff.mp hi, zero_add]
  have hfinite : E.Finite := by
    rw [hE]
    exact (Finset.Iic r).finite_toSet
  refine ⟨hfinite, fun d => hmem d, ?_, hcard b⟩
  change E.ncard = ∏ i : σ, (b i - p.degreeOf i + 1)
  rw [hE, Set.ncard_coe_finset, hcard]
  rfl
