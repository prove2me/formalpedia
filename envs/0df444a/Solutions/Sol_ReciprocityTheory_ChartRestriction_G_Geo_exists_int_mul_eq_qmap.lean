-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.exists_int_mul_eq_qmap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:24:08.881249+00:00
-- url     : https://prove2.me/submissions/5e7d321d-1e45-49b3-b324-31eea81c98f0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodB

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
theorem _root_.solution (q : MvPolynomial σ ℚ) :
    ∃ D : ℤ, D ≠ 0 ∧ ∃ q' : MvPolynomial σ ℤ, (D : MvPolynomial σ ℚ) * q = qmap q' := by
  induction q using MvPolynomial.induction_on' with
  | monomial u a =>
    refine ⟨a.den, by exact_mod_cast a.den_nz, MvPolynomial.monomial u a.num, ?_⟩
    rw [show ((a.den : ℤ) : MvPolynomial σ ℚ) = C ((a.den : ℤ) : ℚ) from (map_intCast (C : ℚ →+* MvPolynomial σ ℚ) _).symm,
      C_mul_monomial, MvPolynomial.map_monomial]
    congr 1
    push_cast
    exact Rat.den_mul_eq_num a
  | add p q hp hq =>
    obtain ⟨D₁, hD₁, p', hp'⟩ := hp
    obtain ⟨D₂, hD₂, q', hq'⟩ := hq
    refine ⟨D₁ * D₂, mul_ne_zero hD₁ hD₂, (D₂ : MvPolynomial σ ℤ) * p' + (D₁ : MvPolynomial σ ℤ) * q', ?_⟩
    rw [map_add, map_mul, map_mul, map_intCast, map_intCast, ← hp', ← hq']
    push_cast
    ring
end ReciprocityTheory.ChartRestriction.G.Geo
