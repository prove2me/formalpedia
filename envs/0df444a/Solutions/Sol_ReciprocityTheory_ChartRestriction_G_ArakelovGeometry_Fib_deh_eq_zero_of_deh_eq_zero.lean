-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.deh_eq_zero_of_deh_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:37:37.444871+00:00
-- url     : https://prove2.me/submissions/d52b2ab6-951b-4d17-8d9b-140163334b53

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsSmoothPts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LemCone
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_homog_isHomogeneous
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_eval__homog_a4d5e8660c60
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_mem_coordIdeal_of_isHomogeneous


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
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
theorem _root_.solution {ι : Type*} [Fintype ι] {Ω : Type*} [Field Ω]
    (x : ι → Ω) (z : ι → ℂ) (i₀ : ι) (hx : x i₀ ≠ 0) (hz : z i₀ ≠ 0)
    (hP : ∀ f ∈ coordIdeal ℤ x, eval z (map (Int.castRingHom ℂ) f) = 0)
    {G : MvPolynomial ι ℤ} (hG : deh x i₀ G = 0) : deh z i₀ G = 0 := by
  classical
  have hH := homog_isHomogeneous i₀ G le_rfl
  have h1 : aeval x (homog i₀ G.totalDegree G) = 0 := by
    rw [aeval_def, algebraMap_int_eq, eval₂_homog x i₀ hx G le_rfl, hG, mul_zero]
  have h2 := hP _ (mem_coordIdeal_of_isHomogeneous ℤ x hH h1)
  rw [eval_map, eval₂_homog z i₀ hz G le_rfl] at h2
  exact (mul_eq_zero.mp h2).resolve_left (pow_ne_zero _ hz)
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
