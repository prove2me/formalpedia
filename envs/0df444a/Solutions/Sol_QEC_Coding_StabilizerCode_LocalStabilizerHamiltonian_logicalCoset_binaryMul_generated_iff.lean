-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.logicalCoset_binaryMul_generated_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:57:12.925195+00:00
-- url     : https://prove2.me/submissions/2b3e9981-d960-431a-8af5-aef0f993752a

import Definitions.Def_QEC_Coding_Stabilizer_Energy
import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
import Theorems.Thm_QEC_Coding_StabilizerCode_generatedVectorSubspace_isotropic
import Theorems.Thm_QEC_Coding_StabilizerCode_vector_mem_generatedVectorSubspace_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_vector_mem_orthogonal_iff_inBinaryNormalizer


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open PauliSymplectic
open scoped Classical
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
open QEC.Coding.StabilizerCode QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
namespace QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
theorem _root_.solution
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (E S : Binary ι) (hS : S ∈ H.code.1.generatedGroup) :
    (H.code.1.InBinaryNormalizer (binaryMul E S) ∧
        ¬ H.code.1.InGeneratedGroupUpToSign (binaryMul E S)) ↔
      (H.code.1.InBinaryNormalizer E ∧
        ¬ H.code.1.InGeneratedGroupUpToSign E) := by
  let V := H.code.1.generatedVectorSubspace
  have hSV : S.vector ∈ V :=
    (H.code.1.vector_mem_generatedVectorSubspace_iff S).2
      ⟨S, hS, rfl⟩
  have hSOrth :
      S.vector ∈ FiniteSymplectic.form.orthogonal V :=
    H.code.1.generatedVectorSubspace_isotropic hSV
  rw [← H.code.1.vector_mem_orthogonal_iff_inBinaryNormalizer,
    ← H.code.1.vector_mem_generatedVectorSubspace_iff,
    ← H.code.1.vector_mem_orthogonal_iff_inBinaryNormalizer,
    ← H.code.1.vector_mem_generatedVectorSubspace_iff]
  change
    (E.vector + S.vector ∈ FiniteSymplectic.form.orthogonal V ∧
        E.vector + S.vector ∉ V) ↔
      (E.vector ∈ FiniteSymplectic.form.orthogonal V ∧ E.vector ∉ V)
  rw [(FiniteSymplectic.form.orthogonal V).add_mem_iff_left hSOrth,
    V.add_mem_iff_left hSV]
end QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
