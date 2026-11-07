-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.logicalCoset_binaryMul_generated_iff_for_strip_cleaning
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:00:02.4459+00:00
-- url     : https://prove2.me/submissions/a373c5f4-debf-4a6b-a715-bf7a1ce40bde

import Definitions.Def_QEC_Coding_Stabilizer_Cleaning
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_AlternatingStripDistance
import Theorems.Thm_QEC_Coding_StabilizerCode_generatedVectorSubspace_isotropic
import Theorems.Thm_QEC_Coding_StabilizerCode_vector_mem_generatedVectorSubspace_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_vector_mem_orthogonal_iff_inBinaryNormalizer


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.StabilizerCode
open QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
open PauliSymplectic
namespace QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
theorem _root_.solution
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
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
