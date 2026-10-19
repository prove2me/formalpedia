-- Prove2me | solution 1 for PermanentRollout.affine_restrictTotalDegree_finrank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.813979+00:00
-- url     : https://prove2.me/submissions/da526a56-a4f3-47ef-b6a5-b02eb64ff81a

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators Topology Pointwise
open Filter Asymptotics
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {ι : Type*} [Fintype ι] (N : ℕ) :
    Module.finrank ℂ (MvPolynomial.restrictTotalDegree ι ℂ N) =
      (N + Fintype.card ι).choose (Fintype.card ι) := by
  classical
  let T : Set (ι →₀ ℕ) := {d | d.degree ≤ N}
  have hT : T.Finite := Finsupp.finite_of_degree_le N
  letI : Fintype T := hT.fintype
  let s : Finset (ι →₀ ℕ) := hT.toFinset
  have hrestrict :
      MvPolynomial.restrictTotalDegree ι ℂ N =
        MvPolynomial.restrictSupport ℂ T := by
    ext p
    simp [MvPolynomial.mem_restrictTotalDegree,
      MvPolynomial.mem_restrictSupport_iff, T,
      MvPolynomial.totalDegree, Finset.sup_le_iff,
      Finsupp.degree_apply, Finsupp.sum, Set.subset_def]
  have hsubtype : Fintype.card T = s.card := by
    let E : T ≃ {d // d ∈ s} :=
      Equiv.subtypeEquiv (Equiv.refl (ι →₀ ℕ)) (by
        intro d
        simp [s, T])
    exact (Fintype.card_congr E).trans (Fintype.card_coe s)
  have hmaps :
      (s : Set (ι →₀ ℕ)).MapsTo Finsupp.degree
        (Finset.range (N + 1) : Set ℕ) := by
    intro d hd
    have hle : d.degree ≤ N := by
      simpa [s, T] using hd
    simp only [Finset.mem_coe, Finset.mem_range]
    omega
  have hfiber (n : ℕ) (hn : n < N + 1) :
      s.filter (fun d => d.degree = n) =
        (Finset.univ : Finset ι).finsuppAntidiag n := by
    ext d
    simp only [Finset.mem_filter, s, Set.Finite.mem_toFinset,
      T, Set.mem_setOf_eq, Finset.mem_finsuppAntidiag,
      Finset.subset_univ, and_true]
    rw [← Finsupp.degree_eq_sum]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨by omega, h⟩
  have hcard := Finset.card_eq_sum_card_fiberwise
    (f := Finsupp.degree) (s := s) (t := Finset.range (N + 1)) hmaps
  calc
    Module.finrank ℂ (MvPolynomial.restrictTotalDegree ι ℂ N) =
        Fintype.card T := by
      rw [hrestrict]
      exact Module.finrank_eq_card_basis
        (MvPolynomial.basisRestrictSupport ℂ T)
    _ = s.card := hsubtype
    _ = ∑ n ∈ Finset.range (N + 1),
          (Fintype.card ι).multichoose n := by
      rw [hcard]
      apply Finset.sum_congr rfl
      intro n hn
      rw [hfiber n (Finset.mem_range.mp hn),
        Finset.card_finsuppAntidiag_nat_eq_multichoose]
      simp
    _ = (N + Fintype.card ι).choose (Fintype.card ι) :=
      Nat.sum_range_multichoose N (Fintype.card ι)
end PermanentRollout
