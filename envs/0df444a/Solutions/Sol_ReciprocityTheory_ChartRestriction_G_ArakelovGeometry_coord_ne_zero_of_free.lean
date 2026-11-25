-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.coord_ne_zero_of_free
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:45:54.285356+00:00
-- url     : https://prove2.me/submissions/f2e871f8-9e96-4e67-a684-62ba2cde640d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_SectionModuleEqSpanPow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_EqZeroOfSecTraceMulEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ExistsNatMulMemConeRingIntFin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ChooseLePowDivFactorial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo Module Filter Asymptotics
variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} [Fintype κ] {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution (y : Fin (D + 1) → Ω) (hy : coordIdeal ℤ y = ⊥) (l : Fin (D + 1)) : y l ≠ 0 := by
  intro h0
  have hX : (MvPolynomial.X l : MvPolynomial (Fin (D + 1)) ℤ) ∈ coordIdeal ℤ y := by
    unfold ReciprocityTheory.ChartRestriction.G.Geo.coordIdeal
    rw [RingHom.mem_ker]
    simp [ReciprocityTheory.ChartRestriction.G.Geo.coneMap, h0]
  rw [hy] at hX
  exact MvPolynomial.X_ne_zero l (Ideal.mem_bot.1 hX)
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
