-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.not_commutes_complement_of_not_commutes_restriction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:43:32.934638+00:00
-- url     : https://prove2.me/submissions/fcfda1f1-4667-4c23-b664-c071c6c8483b

import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_AlternatingStripDistance
import Definitions.Def_QEC_Coding_Stabilizer_SupportEnergyBounds
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_StripLogicalPath
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_binaryMul_complement_vector
import Theorems.Thm_QEC_Coding_PauliSymplectic_commutes_binaryMul_right
import Theorems.Thm_QEC_Coding_PauliSymplectic_commutes_comm
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_generator_mem_generatedGroup


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open PauliSymplectic
open scoped Classical
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
open QEC.Coding.StabilizerCode QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
variable {κ : Type*} [Fintype κ]
namespace QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
theorem _root_.solution
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (Q E F : Binary ι) (j : κ)
    (hQNormalizer : H.code.1.InBinaryNormalizer Q)
    (hdecomp : Q.vector = E.vector + F.vector)
    (hE : ¬ Commutes E (H.generators j)) :
    ¬ Commutes F (H.generators j) := by
  intro hF
  have hQ : Commutes Q (H.generators j) :=
    hQNormalizer (H.generators j) (H.generator_mem_generatedGroup j)
  have hproduct :
      Commutes (H.generators j) (binaryMul Q F) :=
    commutes_binaryMul_right
      ((commutes_comm _ _).2 hQ) ((commutes_comm _ _).2 hF)
  apply hE
  change symplecticForm E.vector (H.generators j).vector = 0
  rw [← binaryMul_complement_vector Q E F hdecomp]
  exact (commutes_comm _ _).2 hproduct
end QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
