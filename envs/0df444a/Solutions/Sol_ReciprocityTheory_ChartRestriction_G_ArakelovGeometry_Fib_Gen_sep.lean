-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.Gen.sep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:54:03.524172+00:00
-- url     : https://prove2.me/submissions/a07b4407-8674-4102-ad5f-71e71e4fa303

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStB

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
variable {ι : Type} [Fintype ι] {Ω : Type*} [Field Ω] {D : ℕ} {x : ι → Ω} {e : Fin (D + 1) → ι}
variable [DecidableEq ι] (G : Gen x e) {w : Fin (D + 1) → ℂ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
namespace Gen
theorem _root_.solution (hw : G.Good w) : (G.P.map (deh w 0)).Separable := by
  have h0 : (G.U * G.P + G.V * Polynomial.derivative G.P - Polynomial.C G.cc).map (deh w 0) = 0 := by
    ext j
    rw [Polynomial.coeff_map, Polynomial.coeff_zero]
    apply hw.ker
    rw [← Polynomial.coeff_map, G.hUV, Polynomial.coeff_zero]
  have h1 : G.U.map (deh w 0) * G.P.map (deh w 0) +
      G.V.map (deh w 0) * Polynomial.derivative (G.P.map (deh w 0)) =
      Polynomial.C (deh w 0 G.cc) := by
    rw [Polynomial.derivative_map, ← sub_eq_zero, ← h0]
    simp only [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C]
  rw [Polynomial.separable_def]
  refine ⟨Polynomial.C (deh w 0 G.cc)⁻¹ * G.U.map (deh w 0),
    Polynomial.C (deh w 0 G.cc)⁻¹ * G.V.map (deh w 0), ?_⟩
  rw [mul_assoc, mul_assoc, ← mul_add, h1, ← Polynomial.C_mul, inv_mul_cancel₀ hw.cc, Polynomial.C_1]
end Gen
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
