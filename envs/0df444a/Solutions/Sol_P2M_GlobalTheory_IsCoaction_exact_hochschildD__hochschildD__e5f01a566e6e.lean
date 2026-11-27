-- Prove2me | solution 1 for P2M_GlobalTheory_IsCoaction_exact_hochschildD__hochschildD__e5f01a566e6e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:51:39.593883+00:00
-- url     : https://prove2.me/submissions/c7dfedcb-c9ce-48d4-b001-d3c419d82a01

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_TupleDifferentialTupleDifferential
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_TensorCoeffOfMemTorusWeightSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsUnitAddMonoidAlgebraIffOfTwoUniqueSums
import Theorems.Thm_GlobalTheory_coe_unitsAddMonoidAlgebraEquiv
import Theorems.Thm_GlobalTheory_trivialCoaction_apply
import Theorems.Thm_P2M_GlobalTheory_hochschildD__trivialCoaction_d0af9f793cf0
import Theorems.Thm_GlobalTheory_hochschild_homotopy_one
import Theorems.Thm_GlobalTheory_mem_coactionWeightSpace
import Theorems.Thm_GlobalTheory_tupleCoface_last
import Theorems.Thm_GlobalTheory_tupleCoface_zero
import Theorems.Thm_GlobalTheory_tupleContraction_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.mem_coactionWeightSpace
attribute [local simp] GlobalTheory.tupleCoface_last
attribute [local simp] GlobalTheory.tupleCoface_zero
attribute [local simp] GlobalTheory.tupleContraction_apply


attribute [local simp] GlobalTheory.coe_unitsAddMonoidAlgebraEquiv
attribute [local simp] GlobalTheory.trivialCoaction_apply
attribute [local simp] GlobalTheory.hochschildD₀_trivialCoaction

set_option autoImplicit false
open TensorProduct Coalgebra AddMonoidAlgebra
open GlobalTheory
variable {R : Type*} [CommRing R] {H : Type*} [Ring H] [Bialgebra R H]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {X : Type*} [AddMonoid X]
namespace GlobalTheory
namespace IsCoaction
theorem _root_.solution {ρ : M →ₗ[R] M ⊗[R] R[X]} (h : IsCoaction ρ) :
    Function.Exact (hochschildD₀ ρ) (hochschildD₁ ρ) := by
  classical
  intro f
  refine ⟨fun hf => ⟨-tensorCoeff R M 0 f, ?_⟩, ?_⟩
  · simpa [hf] using hochschild_homotopy_one ρ f
  · rintro ⟨m, rfl⟩
    let := h.decomposition
    induction m using DirectSum.Decomposition.inductionOn (torusWeightSpace ρ) with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb, add_zero]
    | homogeneous m =>
      simp [hochschildD₀, hochschildD₁, mem_coactionWeightSpace.1 m.2, one_def]
end IsCoaction
end GlobalTheory
