-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.i2comp_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:05:22.334107+00:00
-- url     : https://prove2.me/submissions/a451faa6-ce5d-4cbc-a6ed-94a553ffd101

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_DoubleBlock
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_EqSumMultihomogeneousComponents
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_i2comp_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_i2comp_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_isMultiHomog_i2comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_i2comp_of_homog
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_eq_sum_multihomogeneous_components
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_i2comp_mul_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
open Classical
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {F : Ideal (MRing ι)} (hF : IsMultiHomogIdeal F) (a : K → ℕ) {u : MRing ι}
    (hu : u ∈ F) : i2comp a u ∈ F := by
  classical
  obtain ⟨S, hS, rfl⟩ := hF
  revert a
  induction hu using Submodule.span_induction with
  | mem x hx =>
    intro a
    obtain ⟨b, hb⟩ := hS x hx
    rw [i2comp_of_homog hb]
    split_ifs
    · exact Ideal.subset_span hx
    · exact zero_mem _
  | zero => intro a; rw [i2comp_zero]; exact zero_mem _
  | add x y _ _ hx hy => intro a; rw [i2comp_add]; exact add_mem (hx a) (hy a)
  | smul r x _ hx =>
    intro a
    rw [smul_eq_mul, eq_sum_multihomogeneous_components r, Finset.sum_mul]
    have : i2comp a (∑ b ∈ r.support.image i2bdeg, i2comp b r * x) =
        ∑ b ∈ r.support.image i2bdeg, i2comp a (i2comp b r * x) := map_sum (i2compHom a) _ _
    rw [this]
    refine Ideal.sum_mem _ fun b _ => ?_
    rw [mul_comm, i2comp_mul_right (isMultiHomog_i2comp b r)]
    split_ifs
    · exact Ideal.mul_mem_right _ _ (hx _)
    · exact zero_mem _
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
