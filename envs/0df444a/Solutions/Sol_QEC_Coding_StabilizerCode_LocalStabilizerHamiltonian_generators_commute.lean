-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.generators_commute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:07:49.163699+00:00
-- url     : https://prove2.me/submissions/eaef3553-4b5e-40a9-9212-d431c37b5245

import Definitions.Def_QEC_Coding_Stabilizer_FixedGeneratorInteraction
import Definitions.Def_QEC_Locality_Core_Definitions
import Definitions.Def_QEC_Coding_Stabilizer_LocalHamiltonian
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_generator_mem_generatedGroup
import Theorems.Thm_QEC_Coding_StabilizerCode_generatedGroup_pairwise_commutes


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.StabilizerCode
open PauliSymplectic
open scoped BigOperators
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
open QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
namespace QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
theorem _root_.solution
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ)) (j k : κ) :
    Commutes (H.generators j) (H.generators k) :=
  H.code.1.generatedGroup_pairwise_commutes
    (H.generator_mem_generatedGroup j) (H.generator_mem_generatedGroup k)
end QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
