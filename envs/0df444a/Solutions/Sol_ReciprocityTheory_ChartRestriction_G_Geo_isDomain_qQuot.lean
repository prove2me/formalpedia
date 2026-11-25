-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.isDomain_qQuot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:28:21.953159+00:00
-- url     : https://prove2.me/submissions/dcce7585-1608-4691-ad85-be8338c20865

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_ratHom_isLocalization

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
noncomputable section
variable {σ : Type}
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution (P : Ideal (MvPolynomial σ ℤ)) (hP : P.IsPrime)
    (hH : P.comap (C : ℤ →+* MvPolynomial σ ℤ) = ⊥) :
    IsDomain (MvPolynomial σ ℚ ⧸ qIdeal P) := by
  let _ := (ratHom P).toAlgebra
  have := ratHom_isLocalization P
  refine IsLocalization.isDomain_of_le_nonZeroDivisors (R := MvPolynomial σ ℤ ⧸ P)
    (M := Algebra.algebraMapSubmonoid (MvPolynomial σ ℤ ⧸ P) (nonZeroDivisors ℤ))
    (S := MvPolynomial σ ℚ ⧸ qIdeal P) ?_
  rintro _ ⟨n, hn, rfl⟩
  apply mem_nonZeroDivisors_of_ne_zero
  intro h0
  rw [eq_intCast, ← map_intCast (Ideal.Quotient.mk P), Ideal.Quotient.eq_zero_iff_mem,
    show (n : MvPolynomial σ ℤ) = C n from (map_intCast (C : ℤ →+* MvPolynomial σ ℤ) n).symm] at h0
  have : n ∈ P.comap (C : ℤ →+* MvPolynomial σ ℤ) := h0
  rw [hH] at this
  exact nonZeroDivisors.ne_zero hn ((Submodule.mem_bot ℤ).mp this)
end ReciprocityTheory.ChartRestriction.G.Geo
