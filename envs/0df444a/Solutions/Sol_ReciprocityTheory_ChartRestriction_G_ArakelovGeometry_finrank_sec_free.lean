-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.finrank_sec_free
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:13:56.874935+00:00
-- url     : https://prove2.me/submissions/577423ff-2e02-4ab6-b63b-b7f066bb6fd9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ProjDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_SectionModuleEqSpanPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo Polynomial Module
variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} [Fintype κ] {D : ℕ}
private theorem coneMap_monomial_one (y : κ → Ω) (s : κ →₀ ℕ) :
    coneMap ℤ y (MvPolynomial.monomial s (1 : ℤ)) =
      C (MvPolynomial.aeval y (MvPolynomial.monomial s (1 : ℤ))) * X ^ s.degree := by
  induction s using Finsupp.induction with
  | zero => simp [coneMap]
  | single_add a b f _ _ ih =>
    rw [MvPolynomial.monomial_single_add, map_mul, ih, map_add, Finsupp.degree_single]
    simp only [coneMap, map_mul, map_pow, MvPolynomial.aeval_X, pow_add, mul_pow]
    ring
private theorem coneMap_of_isHomogeneous (y : κ → Ω) {p : MvPolynomial κ ℤ} {n : ℕ}
    (hp : p.IsHomogeneous n) : coneMap ℤ y p = C (MvPolynomial.aeval y p) * X ^ n := by
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : d.degree = n := by
    have := hp (MvPolynomial.mem_support_iff.mp hd)
    rw [Finsupp.degree_eq_weight_one]
    exact this
  rw [show MvPolynomial.monomial d (p.coeff d) = (p.coeff d) • MvPolynomial.monomial d (1 : ℤ) by
        rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]]
  rw [map_smul, map_smul, coneMap_monomial_one, hdeg, ← smul_mul_assoc, Polynomial.smul_C]
private theorem finrank_homog (n : ℕ) :
    finrank ℤ (MvPolynomial.homogeneousSubmodule (Fin (D + 1)) ℤ n) = (n + D).choose D := by
  have hs : {d : Fin (D + 1) →₀ ℕ | d.degree = n} =
      ((Finset.univ.finsuppAntidiag n : Finset (Fin (D + 1) →₀ ℕ)) : Set (Fin (D + 1) →₀ ℕ)) := by
    ext d; simp [Finset.mem_finsuppAntidiag, Finsupp.degree_eq_sum]
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported, hs,
    (AddMonoidAlgebra.supportedEquivFinsupp _).finrank_eq, Module.finrank_finsupp_self]
  simp only [Finset.coe_sort_coe, Fintype.card_coe, Finset.card_finsuppAntidiag_nat_eq_choose,
    Finset.card_univ, Fintype.card_fin]
  rw [show D + 1 + n - 1 = n + D by omega]
  exact Nat.choose_symm_add
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo Polynomial Module
variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} [Fintype κ] {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution (y : Fin (D + 1) → Ω) (hy : coordIdeal ℤ y = ⊥) (n : ℕ) :
    finrank ℤ (sec ℤ y n) = (n + D).choose D := by
  set H := MvPolynomial.homogeneousSubmodule (Fin (D + 1)) ℤ n
  set f := ((MvPolynomial.aeval y : MvPolynomial (Fin (D + 1)) ℤ →ₐ[ℤ] Ω).toLinearMap).domRestrict H
  have hinj : Function.Injective f := by
    refine (injective_iff_map_eq_zero f).mpr fun p hp => ?_
    have hp' : MvPolynomial.aeval y (p : MvPolynomial (Fin (D + 1)) ℤ) = 0 := hp
    have hmem : (p : MvPolynomial (Fin (D + 1)) ℤ) ∈ coordIdeal ℤ y := by
      rw [coordIdeal, RingHom.mem_ker, coneMap_of_isHomogeneous y p.2, hp']
      simp
    rw [hy, Ideal.mem_bot] at hmem
    exact Subtype.ext hmem
  have hr : LinearMap.range f = sec ℤ y n := LinearMap.range_domRestrict _ _
  rw [← finrank_homog (D := D) n, ← hr]
  exact (LinearEquiv.ofInjective f hinj).finrank_eq.symm
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
