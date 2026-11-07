-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.generatedByMeeting_mem_generatedGroup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:54:54.753313+00:00
-- url     : https://prove2.me/submissions/ceb149c6-b23e-401b-b841-753896c55afb

import Definitions.Def_QEC_Coding_Stabilizer_LocalHamiltonian
import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Coding_Stabilizer_Cleaning

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
    (R : Finset ι) (S : Binary ι)
    (hS : H.GeneratedByMeeting R S) :
    S ∈ H.code.1.generatedGroup := by
  rw [← H.generated_eq]
  change GeneratedStabilizer H.generators S
  induction hS with
  | one => exact .one
  | generator j => exact .generator j.1
  | mul _ _ ihS ihT => exact .mul ihS ihT
  | dagger _ ihS => exact .dagger ihS
end QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
