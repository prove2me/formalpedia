-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.H1.RB.phi_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:51:14.879243+00:00
-- url     : https://prove2.me/submissions/dbdbeb12-25a3-4b88-b484-9f66d1ae20fb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ReducedBasisStatement
import Definitions.Def_ReciprocityTheory_ReducedBases_LatticeReduction
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_IndepOfFlag
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_RB_V_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_RB_phi_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_RB_phi_V
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.H1.RB
open Finset InnerProductSpace Submodule Module ReciprocityTheory.ReducedBases.T2
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section phi
variable {d : ℕ} (u : Fin d → E) (k : Fin d)
private lemma sub_gs_mem_V : u k - gs u k ∈ V u k.val := by
  rw [← V_eq, ← span_gramSchmidt_Iio ℝ u k]
  show u k - gramSchmidt ℝ u k ∈ span ℝ (gramSchmidt ℝ u '' Set.Iio k)
  rw [gramSchmidt_def ℝ u k, sub_sub_cancel]
  refine _root_.sum_mem fun i hi => ?_
  have hsub : (ℝ ∙ gramSchmidt ℝ u i) ≤ span ℝ (gramSchmidt ℝ u '' Set.Iio k) :=
    Submodule.span_mono (Set.singleton_subset_iff.2 ⟨i, Finset.mem_Iio.1 hi, rfl⟩)
  apply hsub
  first
  | exact Submodule.starProjection_apply_mem _ _
  | (rw [Submodule.starProjection_apply]; exact Submodule.coe_mem _)
  | simp
end phi
end ReciprocityTheory.ChartRestriction.G.H1.RB
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1 ReciprocityTheory.ChartRestriction.G.H1.RB
open Finset InnerProductSpace Submodule Module ReciprocityTheory.ReducedBases.T2
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {d : ℕ} (u : Fin d → E) (k : Fin d)
namespace ReciprocityTheory.ChartRestriction.G.H1.RB
theorem _root_.solution (hu : LinearIndependent ℝ u) : phi u k (u k) = 1 := by
  have hne : gs u k ≠ 0 := by
    first
    | exact gramSchmidt_ne_zero ℝ k hu
    | exact gramSchmidt_ne_zero k hu
    | exact gramSchmidt_ne_zero (𝕜 := ℝ) (n := k) hu
  have h1 : phi u k (u k) = phi u k (gs u k) + phi u k (u k - gs u k) := by
    rw [← phi_add]; congr 1; abel
  rw [h1, phi_V u k (sub_gs_mem_V u k), add_zero, phi, real_inner_self_eq_norm_sq,
    div_self (pow_ne_zero 2 (norm_ne_zero_iff.2 hne))]
end ReciprocityTheory.ChartRestriction.G.H1.RB
