-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.unitDefectEnergy_binaryMul_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:07:21.342679+00:00
-- url     : https://prove2.me/submissions/8e4f3126-b8a8-4ecc-bfcc-17816b746f9a

import Definitions.Def_QEC_Coding_Stabilizer_Energy
import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_violatedGenerators_binaryMul_subset

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
    (E F : Binary ι) :
    H.unitDefectEnergy (binaryMul E F) ≤
      H.unitDefectEnergy E + H.unitDefectEnergy F := by
  calc
    _ ≤ (H.violatedGenerators E ∪ H.violatedGenerators F).card :=
      Finset.card_le_card (H.violatedGenerators_binaryMul_subset E F)
    _ ≤ (H.violatedGenerators E).card +
        (H.violatedGenerators F).card :=
      Finset.card_union_le _ _
    _ = _ := rfl
end QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
