-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.sumBd_posDef_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:37:30.01389+00:00
-- url     : https://prove2.me/submissions/6f88464d-d5ed-49ae-a852-8d19e3c4602a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatementPfA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up
open Matrix Topology Filter
open scoped Matrix ComplexOrder ENNReal
noncomputable section
variable {p q : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up
theorem _root_.solution {Z : Matrix (Fin p) (Fin q) ℂ} (hZ : (1 - Z * Zᴴ).PosDef) :
    (1 - Zᴴ * Z).PosDef := by
  set P := 1 - Z * Zᴴ
  have hQ : (1 + Zᴴ * P⁻¹ * Z).PosDef :=
    PosDef.one.add_posSemidef (hZ.inv.posSemidef.conjTranspose_mul_mul_same Z)
  have hPi : P * P⁻¹ = 1 := mul_nonsing_inv P (isUnit_iff_ne_zero.mpr hZ.det_pos.ne')
  have hm : (1 + Zᴴ * P⁻¹ * Z) * (1 - Zᴴ * Z) = 1 := by
    have : Zᴴ * P⁻¹ * Z - Zᴴ * P⁻¹ * (Z * Zᴴ) * Z = Zᴴ * Z := by
      calc Zᴴ * P⁻¹ * Z - Zᴴ * P⁻¹ * (Z * Zᴴ) * Z = Zᴴ * (P⁻¹ * (1 - Z * Zᴴ)) * Z := by
            simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
        _ = Zᴴ * Z := by
            rw [nonsing_inv_mul P (isUnit_iff_ne_zero.mpr hZ.det_pos.ne'), Matrix.mul_one]
    calc (1 + Zᴴ * P⁻¹ * Z) * (1 - Zᴴ * Z)
        = 1 - Zᴴ * Z + (Zᴴ * P⁻¹ * Z - Zᴴ * P⁻¹ * (Z * Zᴴ) * Z) := by
          simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
          abel
      _ = 1 := by rw [this]; abel
  have hm' : (1 - Zᴴ * Z) * (1 + Zᴴ * P⁻¹ * Z) = 1 := mul_eq_one_comm.mp hm
  rw [← inv_eq_left_inv hm']
  exact hQ.inv
end ReciprocityTheory.ChartRestriction.G.AR.Up
