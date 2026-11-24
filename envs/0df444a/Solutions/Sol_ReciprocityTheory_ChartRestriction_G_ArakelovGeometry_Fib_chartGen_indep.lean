-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.chartGen_indep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:26:49.315139+00:00
-- url     : https://prove2.me/submissions/a17188db-867f-4944-bc69-2a8b68b82a8f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_EqZeroOfSecTraceMulEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStD
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_coord_ne_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_coe_dehK
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_aeval_chartGen
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_eval__homog_a4d5e8660c60
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_deh_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_homog_isHomogeneous
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_TraceNormBounds_coord_ne_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_mem_coordIdeal_of_isHomogeneous

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
theorem _root_.solution (y : Fin (D + 1) → Ω) (hfree : coordIdeal ℤ y = ⊥) :
    AlgebraicIndependent ℤ (chartGen y) := by
  classical
  rw [algebraicIndependent_iff_injective_aeval, injective_iff_map_eq_zero]
  intro g hg
  have hy0 := coord_ne_zero y hfree 0
  set G := MvPolynomial.rename Subtype.val g
  have h1 : deh y 0 G = 0 := by
    rw [← aeval_chartGen]
    change (((MvPolynomial.aeval (chartGen y) g : fnField y)) : Ω) = 0
    rw [hg]; rfl
  have hH := homog_isHomogeneous (0 : Fin (D + 1)) G le_rfl
  have h2 : MvPolynomial.aeval y (homog 0 G.totalDegree G) = 0 := by
    rw [MvPolynomial.aeval_def, algebraMap_int_eq, eval₂_homog y 0 hy0 G le_rfl, h1, mul_zero]
  have h3 := mem_coordIdeal_of_isHomogeneous ℤ y hH h2
  rw [hfree, Ideal.mem_bot] at h3
  apply MvPolynomial.funext
  intro u
  let v : Fin (D + 1) → ℚ := fun k => if h : k = 0 then 1 else (u ⟨k, h⟩ : ℚ)
  have h4 := eval₂_homog v 0 (by simp [v]) G le_rfl
  rw [h3, MvPolynomial.eval₂_zero] at h4
  have h5 : deh v 0 G = ((MvPolynomial.eval u g : ℤ) : ℚ) := by
    rw [deh_apply, MvPolynomial.eval₂_rename, MvPolynomial.eval, MvPolynomial.coe_eval₂Hom,
      ← eq_intCast (Int.castRingHom ℚ), MvPolynomial.eval₂_comp_left]
    congr 1
    funext k
    simp [v, k.2]
  rw [h5] at h4
  have h6 : ((MvPolynomial.eval u g : ℤ) : ℚ) = 0 := by
    have := h4.symm
    rwa [mul_eq_zero, or_iff_right (pow_ne_zero _ (by simp [v]))] at this
  simpa using h6
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
