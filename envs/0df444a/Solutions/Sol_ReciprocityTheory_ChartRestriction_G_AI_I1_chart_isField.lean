-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.chart_isField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:08:00.666837+00:00
-- url     : https://prove2.me/submissions/3acfaa78-9b02-42d8-b199-2a42492fd0e3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsMonomialNotMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CurvePt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_isMultiHomog_of_mem_weighted
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_exists_homog_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_chartIdeal_ne_top
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_isUnit_mk_chartIdeal_form

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {F : Type*} [Field F]
variable {W : Ideal (MRingOver F ι)}
namespace ReciprocityTheory.ChartRestriction.G.AI.I1
theorem _root_.solution (hW : IsProjVarF W 0) {j : ∀ k, ι k} (hj : IsChart W j) :
    IsField (MRingOver F ι ⧸ chartIdeal W j) := by
  classical
  haveI := hW.1.1
  have hnt : Nontrivial (MRingOver F ι ⧸ chartIdeal W j) :=
    Ideal.Quotient.nontrivial_iff.mpr (chartIdeal_ne_top hW.1.2.1 hj)
  refine ⟨exists_pair_ne _, mul_comm, fun {y} hy => ?_⟩
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨e₀, h⟩ := exists_homog_chart W j b
  obtain ⟨b', hb', eb⟩ := h e₀ le_rfl
  have hb'W : b' ∉ W := fun h => hy (by
    rw [← eb]; exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left h))
  have hu := isUnit_mk_chartIdeal_form hW j (isMultiHomog_of_mem_weighted hb') hb'W
  rw [eb] at hu
  exact hu.exists_right_inv
end ReciprocityTheory.ChartRestriction.G.AI.I1
