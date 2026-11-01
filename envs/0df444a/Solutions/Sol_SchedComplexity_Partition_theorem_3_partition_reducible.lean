-- Prove2me | solution 1 for SchedComplexity.Partition.theorem_3_partition_reducible
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T12:08:39.803476+00:00
-- url     : https://prove2.me/submissions/b0eed27d-2a96-453d-8184-3125ad233e26
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SchedComplexity_Partition_PartitionProblem
import Definitions.Def_SchedComplexity_Partition_TwoMachineModel
import Definitions.Def_SchedComplexity_Partition_Languages
import Definitions.Def_SchedComplexity_Partition_Constructions
import Theorems.Thm_SchedComplexity_Partition_partition_twoMachine_encoding_reduction
import Theorems.Thm_SchedComplexity_Partition_theorem_3a_equivalence
import Theorems.Thm_SchedComplexity_Partition_theorem_3b_equivalence

open SchedComplexity.Partition

theorem solution :
    CookPvsNP.PolyReducible partitionLang cmaxLang ∧
      CookPvsNP.PolyReducible partitionLang sumWCLang := by
  rcases partition_twoMachine_encoding_reduction with ⟨⟨fA, hfA_poly, hfA⟩, ⟨fB, hfB_poly, hfB⟩⟩
  refine ⟨⟨fA, hfA_poly, fun c => ?_⟩, ⟨fB, hfB_poly, fun c => ?_⟩⟩
  · rw [← hfA c]
    constructor
    · rintro ⟨a, ha, hsol, rfl⟩
      exact ⟨a, ha, (theorem_3a_equivalence a ha).mp hsol, rfl⟩
    · rintro ⟨a, ha, hsched, rfl⟩
      exact ⟨a, ha, (theorem_3a_equivalence a ha).mpr hsched, rfl⟩
  · rw [← hfB c]
    constructor
    · rintro ⟨a, ha, hsol, rfl⟩
      exact ⟨a, ha, (theorem_3b_equivalence a ha).mp hsol, rfl⟩
    · rintro ⟨a, ha, hsched, rfl⟩
      exact ⟨a, ha, (theorem_3b_equivalence a ha).mpr hsched, rfl⟩
