-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.rorth_exists_ext
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:14:03.212007+00:00
-- url     : https://prove2.me/submissions/dacfa2fd-2c17-416b-b7bc-43708fc4ed0a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasimirGapAtNoncompactWeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_Unitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_RorthFunctionalEqZero

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
variable {n : ℕ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D} {V : Submodule ℂ D}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (hVf : FiniteDimensional ℂ V) (j : V →ₗ[ℂ] H) :
    ∃ φ : H →L[ℂ] H, ∀ v : V, φ ((v : D) : H) = j v := by
  let ι : V →ₗ[ℂ] H := D.subtype.comp V.subtype
  have hι : Function.Injective ι := D.injective_subtype.comp V.injective_subtype
  let S : Submodule ℂ H := LinearMap.range ι
  have : FiniteDimensional ℂ S := inferInstance
  have : CompleteSpace S := FiniteDimensional.complete ℂ S
  let e : V ≃ₗ[ℂ] S := LinearEquiv.ofInjective ι hι
  refine ⟨(LinearMap.toContinuousLinearMap (j.comp e.symm.toLinearMap)).comp
    S.orthogonalProjectionOnto, fun v => ?_⟩
  have h1 : S.orthogonalProjectionOnto ((v : D) : H) = e v :=
    S.orthogonalProjectionOnto_mem_subspace_eq_self (e v)
  simp [h1]
end ReciprocityTheory.ChartRestriction.DS
