-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.RgC.posDef_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:36:42.681805+00:00
-- url     : https://prove2.me/submissions/ffe9d522-3e47-4bbe-90ba-b5b85f9d2243

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_RhGradStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_RhGradStatementPfB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.RgC
open Matrix Topology Filter
open scoped ComplexOrder Matrix ContDiff
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.RgC
theorem _root_.solution {r s : ℕ} {Z : Matrix (Fin r) (Fin s) ℂ} (h : (1 - Z * Zᴴ).PosDef) :
    (1 - Zᴴ * Z).PosDef := by
  have hu : IsUnit (1 - Z * Zᴴ).det := isUnit_iff_ne_zero.2 h.det_pos.ne'
  set S := (1 - Z * Zᴴ)⁻¹ with hS
  have hAS : (1 - Z * Zᴴ) * S = 1 := Matrix.mul_nonsing_inv _ hu
  have key : (1 - Zᴴ * Z) * (1 + Zᴴ * S * Z) = 1 := by
    have e : (1 - Zᴴ * Z) * (1 + Zᴴ * S * Z) = 1 + Zᴴ * ((1 - Z * Zᴴ) * S - 1) * Z := by
      simp only [Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul, Matrix.one_mul,
        Matrix.mul_one, Matrix.mul_assoc]
      abel
    rw [e, hAS, sub_self, Matrix.mul_zero, Matrix.zero_mul, add_zero]
  have hinv : (1 - Zᴴ * Z)⁻¹ = 1 + Zᴴ * S * Z := Matrix.inv_eq_right_inv key
  have hP : (1 + Zᴴ * S * Z).PosDef :=
    PosDef.one.add_posSemidef ((h.inv).posSemidef.conjTranspose_mul_mul_same Z)
  rw [← hinv] at hP
  exact Matrix.posDef_inv_iff.1 hP
end ReciprocityTheory.ChartRestriction.G.AR.Up.RgC
