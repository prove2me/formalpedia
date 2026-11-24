-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.aeval_chartGen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:19:44.683141+00:00
-- url     : https://prove2.me/submissions/825aaeb4-9d4a-4538-8b45-5240ebc3db2b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_EqZeroOfSecTraceMulEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStD
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_coe_dehK
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_deh_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.coe_dehK

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Polynomial Module
variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
theorem _root_.solution (y : Fin (D + 1) → Ω) (g : MvPolynomial {k : Fin (D + 1) // k ≠ 0} ℤ) :
    ((MvPolynomial.aeval (chartGen y) g : fnField y) : Ω) =
      deh y 0 (MvPolynomial.rename Subtype.val g) := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [deh_apply]
  | add p q hp hq => simp only [map_add, AddMemClass.coe_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.rename_X, MulMemClass.coe_mul, hp]
    congr 1
    simp [deh_apply, chartGen]
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
