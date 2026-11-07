-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.btExcessEnergy_le_two_mul_participationBound_of_weight_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:18:15.172048+00:00
-- url     : https://prove2.me/submissions/94b168f9-d785-4f51-8d3a-a350e4f48623

import Definitions.Def_QEC_Coding_Stabilizer_Energy
import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_unitDefectEnergy_le_participationBound_of_weight_le_one

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
    (step : Binary ι) (hstep : weight step ≤ 1) :
    H.btExcessEnergy step ≤ 2 * H.participationBound := by
  exact Nat.mul_le_mul_left 2
    (H.unitDefectEnergy_le_participationBound_of_weight_le_one step hstep)
end QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
