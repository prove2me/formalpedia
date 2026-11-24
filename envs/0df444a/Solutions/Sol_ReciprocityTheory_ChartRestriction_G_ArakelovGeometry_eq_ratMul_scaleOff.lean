-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.eq_ratMul_scaleOff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:13:56.162318+00:00
-- url     : https://prove2.me/submissions/af019ee4-6c85-4ad2-bd20-f5712a0244f6

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
open Classical
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution (x : κ → Ω) (e : Fin (D + 1) → κ) {m : ℕ} (hm : 0 < m) (i : κ) :
    x i = algebraMap ℚ Ω (if i ∈ Set.range e then 1 else (m : ℚ)⁻¹) * scaleOff e m x i := by

  have hm' : (m : Ω) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  simp only [scaleOff]
  split_ifs <;> simp_all
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
