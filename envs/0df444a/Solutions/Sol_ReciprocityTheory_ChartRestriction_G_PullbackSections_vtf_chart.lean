-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.vtf_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:45:54.836334+00:00
-- url     : https://prove2.me/submissions/da31a6de-eb42-4b0e-be8d-92e76644b59f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_VtFrRdHol
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_VtFrRdA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_vtfQ_snd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Opposite
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) {x0 : Sp ℂ ⟶ S}
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution (k : ℤ) (a : Over.mk x0 ⟶ A) (i : Fin 1 → L.ι) (h : ⊤ ≤ a.left ⁻¹ᵁ L.U (i 0)) :
    ⊤ ≤ (vtfQ A a).left ⁻¹ᵁ (LPow A L k (Over.mk x0)).U i := by
  intro x _
  have hx : a.left.base x ∈ L.U (i 0) := h (by trivial)
  have hx' : (snd (Over.mk x0) A).left.base ((vtfQ A a).left.base x) ∈ L.U (i 0) := by
    have e : ((vtfQ A a).left ≫ (snd (Over.mk x0) A).left).base x = a.left.base x := by
      rw [vtfQ_snd]
    change ((vtfQ A a).left ≫ (snd (Over.mk x0) A).left).base x ∈ L.U (i 0)
    rw [e]
    exact hx
  refine Set.mem_iInter.mpr fun k => ?_
  rw [Fin.fin_one_eq_zero k]
  exact hx'
end ReciprocityTheory.ChartRestriction.G.PullbackSections
