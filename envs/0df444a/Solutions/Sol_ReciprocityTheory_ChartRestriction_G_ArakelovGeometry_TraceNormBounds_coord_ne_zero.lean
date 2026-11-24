-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds.coord_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:27:31.90511+00:00
-- url     : https://prove2.me/submissions/52208195-56a6-41b4-8ea0-16ae5132d799

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ProjDefs
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsBisFurther
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ProjectiveFrameCoordNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Polynomial Module
variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
theorem _root_.solution {o : Type*} [CommRing o] [Algebra o Ω] [Nontrivial o] {ι : Type*}
    (y : ι → Ω) (h : coordIdeal o y = ⊥) (k : ι) : y k ≠ 0 := by
  intro hk
  have : (MvPolynomial.X k : MvPolynomial ι o) ∈ coordIdeal o y := by
    simp [coordIdeal, coneMap, RingHom.mem_ker, hk]
  rw [h, Ideal.mem_bot] at this
  exact MvPolynomial.X_ne_zero k this
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
