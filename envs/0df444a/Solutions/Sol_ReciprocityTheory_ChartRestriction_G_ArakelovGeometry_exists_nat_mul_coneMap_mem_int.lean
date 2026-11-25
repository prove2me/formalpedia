-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.exists_nat_mul_coneMap_mem_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:41:57.511246+00:00
-- url     : https://prove2.me/submissions/edff76d0-7d8b-40a4-b849-381ca4de54de

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ProjDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ExistsNatMulMemConeRingIntFin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo Polynomial
variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} [Finite κ] {D : ℕ}
variable {ι : Type*}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution (y : ι → Ω) (p : MvPolynomial ι ℚ) :
    ∃ n : ℕ, 0 < n ∧ (n : (Polynomial Ω)) * coneMap ℚ y p ∈ coneRing ℤ y := by

  refine MvPolynomial.induction_on
    (motive := fun p => ∃ n : ℕ, 0 < n ∧ (n : Polynomial Ω) * coneMap ℚ y p ∈ coneRing ℤ y) p ?_ ?_ ?_
  · intro a
    refine ⟨a.den, a.den_pos, ?_⟩
    have h1 : coneMap ℚ y (MvPolynomial.C a) = algebraMap ℚ (Polynomial Ω) a := by
      simp only [coneMap, MvPolynomial.aeval_C]
    have h2 : (a.den : Polynomial Ω) * algebraMap ℚ (Polynomial Ω) a =
        algebraMap ℚ (Polynomial Ω) (a * a.den) := by
      rw [map_mul, map_natCast, mul_comm]
    rw [h1, h2, Rat.mul_den_eq_num, map_intCast]
    exact intCast_mem _ _
  · rintro f g ⟨n1, hn1, h1⟩ ⟨n2, hn2, h2⟩
    refine ⟨n1 * n2, Nat.mul_pos hn1 hn2, ?_⟩
    have h : ((n1 * n2 : ℕ) : Polynomial Ω) * coneMap ℚ y (f + g) =
        (n2 : Polynomial Ω) * ((n1 : Polynomial Ω) * coneMap ℚ y f) +
        (n1 : Polynomial Ω) * ((n2 : Polynomial Ω) * coneMap ℚ y g) := by
      rw [map_add]; push_cast; ring
    rw [h]
    exact add_mem (mul_mem (natCast_mem _ _) h1) (mul_mem (natCast_mem _ _) h2)
  · rintro f i ⟨n, hn, h⟩
    refine ⟨n, hn, ?_⟩
    have hX : coneMap ℚ y (MvPolynomial.X i) ∈ coneRing ℤ y := by
      rw [coneRing, AlgHom.mem_range]
      exact ⟨MvPolynomial.X i, by simp [coneMap]⟩
    rw [map_mul, ← mul_assoc]
    exact mul_mem h hX
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
