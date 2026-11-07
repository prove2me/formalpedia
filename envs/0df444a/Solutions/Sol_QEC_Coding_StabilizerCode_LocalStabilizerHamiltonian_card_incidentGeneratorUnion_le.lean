-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.card_incidentGeneratorUnion_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:34:27.208193+00:00
-- url     : https://prove2.me/submissions/17971046-7d3d-45d8-beee-8bb42e652b56

import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
import Definitions.Def_QEC_Coding_Stabilizer_SupportEnergyBounds
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_incidentGenerators_card_le


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
    (R : Finset ι) :
    (H.incidentGeneratorUnion R).card ≤
      R.card * H.participationBound := by
  exact
    Finset.card_biUnion_le_card_mul R H.incidentGenerators
      H.participationBound fun i _hi => H.incidentGenerators_card_le i
end QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
