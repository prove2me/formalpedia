-- Prove2me | solution 1 for QEC.Locality.support_relative_embeddedLocalPauli_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T16:47:21.752514+00:00
-- url     : https://prove2.me/submissions/afc17a75-c7df-4560-9d3f-69d3d451d207

import Definitions.Def_QEC_Coding_Stabilizer_Correctability
import Definitions.Def_QEC_Coding_Stabilizer_Distance
import Definitions.Def_QEC_Locality_CorrectableRegions_LocalPauliErasureTransfer
import Definitions.Def_QEC_Locality_CorrectableRegions_SemanticDistanceErasure
import Theorems.Thm_QEC_Locality_support_embeddedLocalPauli_subset
import Theorems.Thm_QEC_Coding_PauliSymplectic_support_binaryMul_subset


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Locality
open QEC Semantics Coding
open scoped TensorProduct
open PauliSymplectic
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution (S : FiniteSubsystem ι)
    (p q : LocalPauliWordIndex S) :
    support (binaryMul (binaryDagger (embeddedLocalPauli S p))
      (embeddedLocalPauli S q)) ⊆ S.selected := by
  refine (support_binaryMul_subset _ _).trans ?_
  rw [support_binaryDagger]
  exact Finset.union_subset
    (support_embeddedLocalPauli_subset S p)
    (support_embeddedLocalPauli_subset S q)
end QEC.Locality
