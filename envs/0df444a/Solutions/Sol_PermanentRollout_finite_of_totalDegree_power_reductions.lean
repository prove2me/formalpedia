-- Prove2me | solution 1 for PermanentRollout.finite_of_totalDegree_power_reductions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.257302+00:00
-- url     : https://prove2.me/submissions/444d7e67-1dd7-4f3b-968a-986460304f67

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {ι B A : Type*} [Fintype ι] [CommRing B] [CommRing A] [Algebra B A]
    (x : ι → A) (q : ℕ) (_hq : 0 < q)
    (remainder : ι → MvPolynomial ι B)
    (hdegree : ∀ i, (remainder i).totalDegree < q)
    (hrel : ∀ i, x i ^ q = MvPolynomial.aeval x (remainder i))
    (hgen : Algebra.adjoin B (Set.range x) = ⊤) :
    Module.Finite B A := by
  classical
  let N : ℕ := Fintype.card ι * q + 1
  let small : Set A :=
    (fun m : ι →₀ ℕ =>
      MvPolynomial.aeval x (MvPolynomial.monomial m (1 : B))) ''
        {m : ι →₀ ℕ | m.degree < N}
  let M : Submodule B A := Submodule.span B small
  have hfinite : small.Finite :=
    (Finsupp.finite_of_degree_lt N).image _
  have hlarge (m : ι →₀ ℕ) (hm : N ≤ m.degree) :
      ∃ i : ι, q ≤ m i := by
    by_contra hnone
    push Not at hnone
    have hbound :
        ∑ i : ι, m i ≤ ∑ _i : ι, q := by
      apply Finset.sum_le_sum
      intro i _
      exact Nat.le_of_lt (hnone i)
    have hbound' :
        ∑ i : ι, m i ≤ Fintype.card ι * q := by
      simpa using hbound
    rw [Finsupp.degree_eq_sum] at hm
    dsimp [N] at hm
    omega
  have hmonomial : ∀ n : ℕ, ∀ m : ι →₀ ℕ,
      m.degree = n →
        MvPolynomial.aeval x (MvPolynomial.monomial m (1 : B)) ∈ M := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro m hm
      by_cases hn : m.degree < N
      · exact Submodule.subset_span ⟨m, hn, rfl⟩
      · obtain ⟨i, hi⟩ := hlarge m (Nat.le_of_not_gt hn)
        let m' : ι →₀ ℕ := m - Finsupp.single i q
        have hdecomp : m' + Finsupp.single i q = m :=
          tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hi)
        have hrest : m'.degree + q = m.degree := by
          rw [← Finsupp.degree_single i q, ← map_add, hdecomp]
        have hfactor :
            MvPolynomial.aeval x (MvPolynomial.monomial m (1 : B)) =
              MvPolynomial.aeval x (MvPolynomial.monomial m' (1 : B)) *
                x i ^ q := by
          conv_lhs => rw [← hdecomp]
          rw [MvPolynomial.monomial_add_single, map_mul, map_pow]
          simp
        rw [hfactor, hrel i, (remainder i).as_sum, map_sum,
          Finset.mul_sum]
        apply M.sum_mem
        intro d hd
        have hdlt : d.degree < q :=
          lt_of_le_of_lt (MvPolynomial.le_totalDegree hd) (hdegree i)
        have hnew : (m' + d).degree < n := by
          rw [map_add]
          omega
        have hmem :
            MvPolynomial.aeval x
              (MvPolynomial.monomial (m' + d) (1 : B)) ∈ M :=
          ih _ hnew (m' + d) rfl
        have hterm :
            MvPolynomial.aeval x (MvPolynomial.monomial m' (1 : B)) *
                MvPolynomial.aeval x
                  (MvPolynomial.monomial d ((remainder i).coeff d)) =
              ((remainder i).coeff d) • MvPolynomial.aeval x
                (MvPolynomial.monomial (m' + d) (1 : B)) := by
          rw [← map_mul, MvPolynomial.monomial_mul]
          simp [Algebra.smul_def, MvPolynomial.aeval_monomial]
        rw [hterm]
        exact M.smul_mem _ hmem
  have hfg : M.FG := Submodule.fg_span hfinite
  have hsurj : Function.Surjective
      (MvPolynomial.aeval x : MvPolynomial ι B →ₐ[B] A) := by
    apply (AlgHom.range_eq_top _).mp
    rw [← Algebra.adjoin_range_eq_range_aeval, hgen]
  have htop : M = (⊤ : Submodule B A) := by
    apply top_unique
    intro a _
    obtain ⟨p, rfl⟩ := hsurj a
    rw [p.as_sum, map_sum]
    apply M.sum_mem
    intro d _
    have hmem := hmonomial d.degree d rfl
    have hterm :
        MvPolynomial.aeval x (MvPolynomial.monomial d (p.coeff d)) =
          (p.coeff d) •
            MvPolynomial.aeval x (MvPolynomial.monomial d (1 : B)) := by
      simp [Algebra.smul_def, MvPolynomial.aeval_monomial]
    rw [hterm]
    exact M.smul_mem _ hmem
  apply Module.Finite.of_fg_top
  rw [← htop]
  exact hfg
end PermanentRollout
