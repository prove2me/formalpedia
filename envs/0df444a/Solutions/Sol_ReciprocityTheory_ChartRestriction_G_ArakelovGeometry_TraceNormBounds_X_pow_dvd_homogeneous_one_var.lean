-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds.X_pow_dvd_homogeneous_one_var
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:39:29.152883+00:00
-- url     : https://prove2.me/submissions/ab226631-132f-4b88-bd94-46a88432b243

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_BasisOfLinearIndependentOfCardEqFinrank
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_XZeroPowDvdOfIsHomogeneousAeval
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
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Polynomial Module
variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
theorem _root_.solution {H : MvPolynomial (Fin (0 + 1)) ℤ} {M m : ℕ} (hH : H.IsHomogeneous M)
    (hm : m ≤ M) : MvPolynomial.X 0 ^ m ∣ H := by
  apply X_pow_dvd_of_le_degrees
  intro d hd
  have hdeg : d.degree = M := by
    by_contra hne
    exact (MvPolynomial.mem_support_iff.mp hd) (hH.coeff_eq_zero hne)
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_one] at hdeg
  omega
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
