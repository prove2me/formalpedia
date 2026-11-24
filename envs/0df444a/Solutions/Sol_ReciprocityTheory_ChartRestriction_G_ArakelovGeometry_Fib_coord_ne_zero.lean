-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.coord_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:05:26.973949+00:00
-- url     : https://prove2.me/submissions/69a0d2cb-9c70-44dc-bd11-2d12f2a8eaf4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_EqZeroOfSecTraceMulEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStD

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Polynomial Module
variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
theorem _root_.solution {ι : Type*} (y : ι → Ω) (h : coordIdeal ℤ y = ⊥) (k : ι) : y k ≠ 0 := by
  intro hk
  have hmem : (MvPolynomial.X k : MvPolynomial ι ℤ) ∈ coordIdeal ℤ y := by
    rw [coordIdeal, RingHom.mem_ker, coneMap]
    simp [hk]
  rw [h, Ideal.mem_bot] at hmem
  exact MvPolynomial.X_ne_zero k hmem
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
