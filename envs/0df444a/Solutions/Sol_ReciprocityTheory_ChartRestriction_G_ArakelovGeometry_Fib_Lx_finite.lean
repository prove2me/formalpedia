-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.Lx_finite
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:49:05.716597+00:00
-- url     : https://prove2.me/submissions/ba12e089-d406-4972-8700-82d294fd200d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_EqZeroOfSecTraceMulEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStD
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_coord_ne_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_coord_div_isIntegral
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_Lx_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_TraceNormBounds_coord_div_isIntegral
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_TraceNormBounds_coord_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Polynomial Module IntermediateField
variable {Ω : Type*} [Field Ω] [CharZero Ω] {ι : Type} [Fintype ι] {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
theorem _root_.solution (x : ι → Ω) (e : Fin (D + 1) → ι) (h : IsProjFrame x e) :
    FiniteDimensional (fnField (x ∘ e)) (Lx x e) := by
  have hx0 : x (e 0) ≠ 0 := coord_ne_zero (x ∘ e) h.free 0
  have hint : ∀ t ∈ Set.range (fun i => x i / x (e 0)), IsIntegral (fnField (x ∘ e)) t := by
    rintro t ⟨i, rfl⟩
    exact (coord_div_isIntegral x e h i).tower_top
  rw [Lx_eq x e hx0]
  exact IntermediateField.finiteDimensional_adjoin hint
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
