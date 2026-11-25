-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gaap_setLIntegral_translate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:43:46.187303+00:00
-- url     : https://prove2.me/submissions/4ae819b6-7da7-4a02-ba14-7c505541304f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsBergDensity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamStA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamStB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamSt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_gaap_mem_ball_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder
variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution (y₀ : Fin D → ℂ) (ρ₀ : ℝ) (F : (Fin D → ℂ) → ENNReal) :
    ∫⁻ y in Metric.ball (0 : Fin D → ℂ) ρ₀, F (y₀ + y) = ∫⁻ y in Metric.ball y₀ ρ₀, F y := by
  have hpre : (fun y => y₀ + y) ⁻¹' Metric.ball y₀ ρ₀ = Metric.ball (0 : Fin D → ℂ) ρ₀ := by
    ext y
    exact gaap_mem_ball_add
  rw [← hpre]
  exact (measurePreserving_add_left volume y₀).setLIntegral_comp_preimage_emb
    (measurableEmbedding_addLeft y₀) F _
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
