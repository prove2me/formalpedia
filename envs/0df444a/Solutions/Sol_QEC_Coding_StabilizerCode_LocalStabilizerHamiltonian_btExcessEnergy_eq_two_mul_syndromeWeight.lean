-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.btExcessEnergy_eq_two_mul_syndromeWeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:55:17.30012+00:00
-- url     : https://prove2.me/submissions/63d3e0bc-7bdc-444d-b5c3-172dea11c7bb

import Definitions.Def_QEC_Coding_Stabilizer_ErrorPath
import Definitions.Def_QEC_Coding_Stabilizer_Energy
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_unitDefectEnergy_eq_syndromeWeight

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.StabilizerCode
open QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
open PauliSymplectic
open scoped Classical
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
namespace QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
theorem _root_.solution
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (E : Binary ι) :
    H.btExcessEnergy E = 2 * H.syndromeWeight E := by
  rw [btExcessEnergy, unitDefectEnergy_eq_syndromeWeight]
end QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
