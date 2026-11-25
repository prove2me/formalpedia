-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.dense_eval_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:11:56.434918+00:00
-- url     : https://prove2.me/submissions/ac1724f4-5184-42f9-98a9-3a99f112c388

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ChooseLePowDivFactorial
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_SupLeL2NormSections
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_SupStMonoNormSqPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LemCone
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CNormSt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_coe_dehK
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.coe_dehK



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder
variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {N : ℕ} {Δ : MvPolynomial (Fin N) ℂ} (hΔ : Δ ≠ 0) :
    Dense {w | eval w Δ ≠ 0} := by
  rw [dense_iff_inter_open]
  rintro U hU ⟨w, hw⟩
  by_contra hne
  apply hΔ
  have h0 : ∀ v ∈ U, eval v Δ = 0 := fun v hv => by
    by_contra h
    exact hne ⟨v, hv, h⟩
  have han : AnalyticOnNhd ℂ (fun v => eval v Δ) Set.univ := AnalyticOnNhd.eval_mvPolynomial Δ
  have hz := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (Set.mem_univ w) (Filter.eventually_of_mem (hU.mem_nhds hw) h0)
  exact MvPolynomial.funext fun v => by simpa using hz (Set.mem_univ v)
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
