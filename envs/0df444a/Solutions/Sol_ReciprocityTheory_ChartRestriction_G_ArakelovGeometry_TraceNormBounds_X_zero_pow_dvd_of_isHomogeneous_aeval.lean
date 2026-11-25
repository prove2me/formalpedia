-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds.X_zero_pow_dvd_of_isHomogeneous_aeval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:46:51.076641+00:00
-- url     : https://prove2.me/submissions/78580f5b-b596-4f84-987e-010fa405e61e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_BasisOfLinearIndependentOfCardEqFinrank
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_XZeroPowDvdOfIsHomogeneousAeval
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_TraceNormBounds_X_pow_dvd_homogeneous_one_var
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Polynomial Module
variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} {D : ℕ}
private theorem X_pow_dvd_of_le_degrees {σ : Type*} (i : σ) (m : ℕ) (p : MvPolynomial σ ℤ)
    (h : ∀ d ∈ p.support, m ≤ d i) : MvPolynomial.X i ^ m ∣ p := by
  classical
  rw [p.as_sum]
  refine Finset.dvd_sum fun d hd => ?_
  have hle : Finsupp.single i m ≤ d := Finsupp.single_le_iff.mpr (h d hd)
  exact ⟨MvPolynomial.monomial (d - Finsupp.single i m) (MvPolynomial.coeff d p), by
    rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul, one_mul, add_tsub_cancel_of_le hle]⟩
private theorem coneMap_of_isHomogeneous_arakelov_geometry {n : ℕ} (y : Fin (D + 1) → Ω) (P : MvPolynomial (Fin (D + 1)) ℤ)
    (hP : P.IsHomogeneous n) :
    coneMap ℤ y P = Polynomial.C (MvPolynomial.aeval y P) * Polynomial.X ^ n := by
  classical
  conv_lhs => rw [P.as_sum]
  conv_rhs => rw [P.as_sum]
  simp only [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : d.degree = n := by
    by_contra hne
    exact (MvPolynomial.mem_support_iff.mp hd) (hP.coeff_eq_zero hne)
  rw [← hdeg, Finsupp.degree_eq_sum]
  simp only [coneMap, MvPolynomial.aeval_monomial]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, ← map_pow, ← map_prod, map_mul,
    eq_intCast, map_intCast]
  ring
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Polynomial Module
variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
theorem _root_.solution (y : Fin (D + 1) → Ω) (hfree : coordIdeal ℤ y = ⊥) (u : Ω) (n m : ℕ)
    (H : Fin (D + 1) → MvPolynomial (Fin (D + 1)) ℤ) (hH : ∀ l, (H l).IsHomogeneous (m + n))
    (hu : ∀ l, y l ^ m * u = MvPolynomial.aeval y (H l)) : MvPolynomial.X 0 ^ m ∣ H 0 := by
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · exact X_pow_dvd_homogeneous_one_var (hH 0) (by omega)
  have hl1 : (⟨1, by omega⟩ : Fin (D + 1)) ≠ 0 := by simp [Fin.ext_iff]
  have hPh : (MvPolynomial.X ⟨1, by omega⟩ ^ m * H 0 - MvPolynomial.X 0 ^ m * H ⟨1, by omega⟩ :
      MvPolynomial (Fin (D + 1)) ℤ).IsHomogeneous (m + (m + n)) :=
    ((MvPolynomial.isHomogeneous_X_pow _ _).mul (hH 0)).sub ((MvPolynomial.isHomogeneous_X_pow _ _).mul (hH _))
  have hPy : MvPolynomial.aeval y (MvPolynomial.X ⟨1, by omega⟩ ^ m * H 0 - MvPolynomial.X 0 ^ m * H ⟨1, by omega⟩ :
      MvPolynomial (Fin (D + 1)) ℤ) = 0 := by
    simp only [map_sub, map_mul, map_pow, MvPolynomial.aeval_X, ← hu]
    ring
  have hP0 : (MvPolynomial.X ⟨1, by omega⟩ ^ m * H 0 - MvPolynomial.X 0 ^ m * H ⟨1, by omega⟩ :
      MvPolynomial (Fin (D + 1)) ℤ) = 0 := by
    have hmem : (MvPolynomial.X ⟨1, by omega⟩ ^ m * H 0 - MvPolynomial.X 0 ^ m * H ⟨1, by omega⟩ :
        MvPolynomial (Fin (D + 1)) ℤ) ∈ coordIdeal ℤ y := by
      rw [coordIdeal, RingHom.mem_ker, coneMap_of_isHomogeneous_arakelov_geometry y _ hPh, hPy]
      simp
    rw [hfree, Ideal.mem_bot] at hmem
    exact hmem
  have hPeq := sub_eq_zero.mp hP0
  apply X_pow_dvd_of_le_degrees
  intro d hd
  have h1 : MvPolynomial.coeff (d + Finsupp.single ⟨1, by omega⟩ m) (MvPolynomial.X 0 ^ m * H ⟨1, by omega⟩) ≠ 0 := by
    rw [← hPeq, MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_monomial_mul', if_pos le_add_self,
      add_tsub_cancel_right, one_mul]
    exact MvPolynomial.mem_support_iff.mp hd
  rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_monomial_mul'] at h1
  split_ifs at h1 with hle
  · have := Finsupp.single_le_iff.mp hle
    simpa [Finsupp.single_apply, Ne.symm hl1] using this
  · exact absurd rfl h1
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
