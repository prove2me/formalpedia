-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds.mem_sec_of_charts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:52:04.638146+00:00
-- url     : https://prove2.me/submissions/14d86b90-f63c-4ac6-9849-e83779942df0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_BasisOfLinearIndependentOfCardEqFinrank
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_XZeroPowDvdOfIsHomogeneousAeval
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_TraceNormBounds_hc_mul_homog
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_TraceNormBounds_X_zero_pow_dvd_of_isHomogeneous_aeval
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
private theorem coord_ne_zero_of_coordIdeal_eq_bot (y : Fin (D + 1) → Ω) (hfree : coordIdeal ℤ y = ⊥) (i : Fin (D + 1)) :
    y i ≠ 0 := by
  intro h0
  have hmem : (MvPolynomial.X i : MvPolynomial (Fin (D + 1)) ℤ) ∈ coordIdeal ℤ y := by
    rw [coordIdeal, RingHom.mem_ker]
    simp [coneMap, h0]
  rw [hfree, Ideal.mem_bot] at hmem
  exact MvPolynomial.X_ne_zero i hmem
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
    (hu : ∀ l, y l ^ m * u = MvPolynomial.aeval y (H l)) : u ∈ sec ℤ y n := by
  have hy0 : y 0 ≠ 0 := coord_ne_zero_of_coordIdeal_eq_bot y hfree 0
  obtain ⟨G, hG⟩ := X_zero_pow_dvd_of_isHomogeneous_aeval y hfree u n m H hH hu
  have hG' : MvPolynomial.X 0 ^ m * MvPolynomial.homogeneousComponent n G = H 0 := by
    rw [← hc_mul_homog (MvPolynomial.isHomogeneous_X_pow (0 : Fin (D + 1)) m) G n, ← hG,
      MvPolynomial.homogeneousComponent_of_mem ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (hH 0)), if_pos rfl]
  refine Submodule.mem_map.mpr ⟨MvPolynomial.homogeneousComponent n G,
    (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.homogeneousComponent_isHomogeneous n G), ?_⟩
  show MvPolynomial.aeval y (MvPolynomial.homogeneousComponent n G) = u
  have h2 := hu 0
  rw [← hG', map_mul, map_pow, MvPolynomial.aeval_X] at h2
  exact (mul_left_cancel₀ (pow_ne_zero m hy0) h2).symm
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
