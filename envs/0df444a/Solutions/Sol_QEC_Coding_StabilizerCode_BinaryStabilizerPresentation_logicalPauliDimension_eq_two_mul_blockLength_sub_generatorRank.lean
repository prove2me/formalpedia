-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.logicalPauliDimension_eq_two_mul_blockLength_sub_generatorRank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T16:42:12.072408+00:00
-- url     : https://prove2.me/submissions/12efd367-c5cc-451b-8c83-e8f503c671d8

import Definitions.Def_QEC_Coding_Stabilizer_Distance
import Definitions.Def_QEC_Coding_Stabilizer_Parameters
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_nondegenerate
import Theorems.Thm_QEC_Coding_StabilizerCode_generatedVectorSubspace_isotropic

section
noncomputable section
namespace QEC
namespace Coding
open PauliSymplectic
universe u v
namespace StabilizerCode
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
namespace BinaryStabilizerPresentation
omit [DecidableEq ι] in
private theorem finrank_symplecticVector :
    Module.finrank (ZMod 2) (SymplecticVector (ZMod 2) ι) =
      2 * Fintype.card ι := by
  rw [(SymplecticVector.toProdLinearEquiv (F := ZMod 2) (ι := ι)).finrank_eq,
    Module.finrank_prod, Module.finrank_pi]
  omega
private theorem generatedVectorSubspace_le_normalizer
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) :
    P.code.1.generatedVectorSubspace ≤
      FiniteSymplectic.form.orthogonal P.code.1.generatedVectorSubspace :=
  P.code.1.generatedVectorSubspace_isotropic
private theorem finrank_stabilizerInNormalizer
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) :
    Module.finrank (ZMod 2) P.stabilizerInNormalizer = P.generatorRank := by
  rw [stabilizerInNormalizer, generatorRank]
  exact (Submodule.comapSubtypeEquivOfLe
    (P.generatedVectorSubspace_le_normalizer)).finrank_eq
private theorem finrank_normalizer
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) :
    Module.finrank (ZMod 2)
      (FiniteSymplectic.form.orthogonal P.code.1.generatedVectorSubspace) =
      2 * P.blockLength - P.generatorRank := by
  rw [LinearMap.BilinForm.finrank_orthogonal FiniteSymplectic.form_nondegenerate,
    finrank_symplecticVector, blockLength, generatorRank]
private theorem generatorRank_le_blockLength
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) :
    P.generatorRank ≤ P.blockLength := by
  have hle := Submodule.finrank_mono P.generatedVectorSubspace_le_normalizer
  rw [P.finrank_normalizer] at hle
  change P.generatorRank ≤ 2 * P.blockLength - P.generatorRank at hle
  omega
end BinaryStabilizerPresentation
namespace StabilizerParameterData
end StabilizerParameterData
end StabilizerCode
end Coding
end QEC
end
end

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open PauliSymplectic
universe u v
open QEC.Coding.StabilizerCode
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
open QEC.Coding.StabilizerCode.BinaryStabilizerPresentation
namespace QEC.Coding.StabilizerCode.BinaryStabilizerPresentation
theorem _root_.solution
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) :
    P.logicalPauliDimension = 2 * (P.blockLength - P.generatorRank) := by
  have hquot := Submodule.finrank_quotient_add_finrank P.stabilizerInNormalizer
  change Module.finrank (ZMod 2) P.logicalPauliSpace =
    2 * (P.blockLength - P.generatorRank)
  rw [P.finrank_stabilizerInNormalizer, P.finrank_normalizer] at hquot
  have hsum : Module.finrank (ZMod 2) P.logicalPauliSpace + P.generatorRank =
      2 * P.blockLength - P.generatorRank := by
    exact hquot
  have hle := P.generatorRank_le_blockLength
  omega
end QEC.Coding.StabilizerCode.BinaryStabilizerPresentation
