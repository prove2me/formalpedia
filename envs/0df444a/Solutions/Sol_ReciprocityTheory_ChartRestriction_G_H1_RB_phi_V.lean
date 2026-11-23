-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.H1.RB.phi_V
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:45:57.360804+00:00
-- url     : https://prove2.me/submissions/cc7efb2c-3225-4f79-9d63-51fd44d667cf

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ReducedBasisStatement
import Definitions.Def_ReciprocityTheory_ReducedBases_LatticeReduction
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_IndepOfFlag
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_RB_V_eq
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
private lemma inner_gs_eq_zero_of_mem_V {x : E} (hx : x ∈ V u k.val) : ⟪gs u k, x⟫_ℝ = 0 := by
  have hx' : x ∈ span ℝ (gramSchmidt ℝ u '' Set.Iio k) := by
    rw [span_gramSchmidt_Iio, V_eq]
    exact hx
  have hle : span ℝ (gramSchmidt ℝ u '' Set.Iio k) ≤ (ℝ ∙ gramSchmidt ℝ u k)ᗮ := by
    rw [Submodule.span_le]
    rintro _ ⟨j, hj, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right]
    exact gramSchmidt_orthogonal ℝ u (ne_of_gt hj)
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.1 (hle hx')
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
theorem _root_.solution {x : E} (hx : x ∈ V u k.val) : phi u k x = 0 := by
  simp [phi, inner_gs_eq_zero_of_mem_V u k hx]
end ReciprocityTheory.ChartRestriction.G.H1.RB
