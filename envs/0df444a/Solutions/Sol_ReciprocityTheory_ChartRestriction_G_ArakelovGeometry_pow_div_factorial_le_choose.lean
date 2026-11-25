-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.pow_div_factorial_le_choose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:04:21.208001+00:00
-- url     : https://prove2.me/submissions/cd42ffa0-2347-4886-a651-3e57a63f328b

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
theorem _root_.solution (m D : ℕ) : ((m : ℝ) ^ D) / (D.factorial : ℝ) ≤ ((m + D).choose D : ℝ) := by
  have h1 : m + D + 1 - D = m + 1 := by omega
  have h2 := Nat.pow_le_choose (α := ℝ) D (m + D)
  rw [h1] at h2
  refine le_trans ?_ h2
  gcongr
  push_cast
  linarith
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
