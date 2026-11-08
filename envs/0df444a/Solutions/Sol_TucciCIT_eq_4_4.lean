-- Prove2me | solution 1 for TucciCIT.eq_4_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T18:58:12.594126+00:00
-- url     : https://prove2.me/submissions/a7fb10ef-6db2-4c9d-bb26-0194d71cbb33

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P20
import Definitions.Def_TucciCIT_metaDensity
import Definitions.Def_TucciCIT_sTanglement

open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P20

open TucciCIT in
theorem solution {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (ψ : Matrix X Y ℂ) :
    sTanglement (metaDensity ψ) =
      subsystemEntropy (metaDensity ψ) (fun p => (p.1, p.2.1)) (fun p => p.2.2) +
        subsystemEntropy (metaDensity ψ) (fun p => (p.1, p.2.2)) (fun p => p.2.1) -
        vnEntropy (metaDensity ψ) -
        subsystemEntropy (metaDensity ψ) (fun p => p.1) (fun p => p.2) := by
  unfold sTanglement
  ring
