-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.UnitaryGroupOfForm.proj_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:25:26.785894+00:00
-- url     : https://prove2.me/submissions/21b0e883-47e8-4ea0-ab03-784f9c914123

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ConjTransposeEqOfInG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_PolarJmConjTranspose
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_IrredA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
open ReciprocityTheory.ChartRestriction.DS.UnitaryGroupOfForm
variable {n : ℕ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
namespace ReciprocityTheory.ChartRestriction.DS.UnitaryGroupOfForm
theorem _root_.solution (T : Submodule ℂ H) [T.HasOrthogonalProjection] (A : H →L[ℂ] H)
    (h1 : ∀ x ∈ T, A x ∈ T) (h2 : ∀ x ∈ Tᗮ, A x ∈ Tᗮ) (x : H) :
    T.starProjection (A x) = A (T.starProjection x) := by
  have hx := Submodule.sub_starProjection_mem_orthogonal (K := T) x
  have e : A x = A (T.starProjection x) + A (x - T.starProjection x) := by
    rw [← map_add, add_sub_cancel]
  rw [e, map_add, Submodule.starProjection_eq_self_iff.mpr (h1 _ (T.starProjection_apply_mem x)),
    (Submodule.starProjection_apply_eq_zero_iff T).mpr (h2 _ hx), add_zero]
end ReciprocityTheory.ChartRestriction.DS.UnitaryGroupOfForm
