-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P85.residue_reducibility
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T22:41:30.778358+00:00
-- url     : https://prove2.me/submissions/55fb5124-e19b-4ebb-94ea-734cc2a92ca5

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P85

noncomputable section

open scoped BigOperators

open QAlgorithms

open QAlgorithms.Papers.Independent.Gap48.P10
  (InZomega InDomega Residue bits residue residueMultiply Reducible)

open QAlgorithms.Papers.Independent.Support21.P13
  (synthesisRing integralRing coordinateValue HTLetter htWordMatrix EntriesInRing cliffordTLibrary)

open QAlgorithms.Papers.Independent.Intakethird100.P85 in
theorem solution (x : Residue) :
    (Reducible x ↔ x ∈ ({bits 0, bits 5, bits 10, bits 15} : Set Residue)) ∧
    (Reducible x ↔ residueMultiply (bits 10) x = bits 0) ∧
    (Reducible x ↔ residueNorm x = bits 0) ∧
    (TwiceReducible x ↔ x = bits 0) := by
  simp only [Reducible, TwiceReducible, residueNorm, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  revert x
  decide +kernel

end
