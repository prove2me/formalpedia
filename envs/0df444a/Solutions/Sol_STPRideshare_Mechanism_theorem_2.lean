-- Prove2me | solution 1 for STPRideshare.Mechanism.theorem_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T04:20:01.084552+00:00
-- url     : https://prove2.me/submissions/f287546e-4ad1-4018-8c6e-d4afdcfd239a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_STPRideshare_Mechanism_theorem_2_temporally_consistent
import Theorems.Thm_STPRideshare_Mechanism_theorem_2_spic
import Theorems.Thm_STPRideshare_Mechanism_theorem_2_rider_ir
import Theorems.Thm_STPRideshare_Mechanism_theorem_2_strict_bb
import Theorems.Thm_STPRideshare_Mechanism_theorem_2_welfare_optimal
import Theorems.Thm_STPRideshare_Mechanism_theorem_2_core_selecting
import Theorems.Thm_STPRideshare_Mechanism_theorem_2_envy_free_drivers
import Theorems.Thm_STPRideshare_Mechanism_theorem_2_envy_free_riders
import Theorems.Thm_STPRideshare_Mechanism_theorem_2_driver_ir

open STPRideshare.Mechanism

theorem solution {L : Type} [Fintype L] (sel : Selector L) (hsel : IsOptimalSelector sel) :
    TemporallyConsistent (stp sel) ∧ SPIC (stp sel) ∧
    RiderIR (stp sel) ∧ StrictBB (stp sel) ∧
    WelfareOptimalFromAnyHistory (stp sel) ∧ CoreSelecting (stp sel) ∧
    EnvyFreeDrivers (stp sel) ∧ EnvyFreeRiders (stp sel) ∧
    DriverIRFromAnyHistory (stp sel) :=
  ⟨theorem_2_temporally_consistent sel hsel, theorem_2_spic sel hsel,
    theorem_2_rider_ir sel hsel, theorem_2_strict_bb sel hsel,
    theorem_2_welfare_optimal sel hsel, theorem_2_core_selecting sel hsel,
    theorem_2_envy_free_drivers sel hsel, theorem_2_envy_free_riders sel hsel,
    theorem_2_driver_ir sel hsel⟩
