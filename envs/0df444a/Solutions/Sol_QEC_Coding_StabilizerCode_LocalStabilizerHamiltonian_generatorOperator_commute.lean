-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.generatorOperator_commute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:31:31.974472+00:00
-- url     : https://prove2.me/submissions/9e95a852-e88e-4941-9cff-274e7b5d68c9

import Definitions.Def_QEC_Coding_Stabilizer_FixedGeneratorInteraction
import Definitions.Def_QEC_Locality_Core_Definitions
import Definitions.Def_QEC_Coding_Stabilizer_LocalHamiltonian
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_generators_commute
import Theorems.Thm_QEC_Coding_PauliSymplectic_toQubitOperator_commute_of_commutes


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
    Commute (H.generatorOperator j) (H.generatorOperator k) := by
  exact toQubitOperator_commute_of_commutes
      (H.generators j) (H.generators k) (H.generators_commute j k)
end QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
