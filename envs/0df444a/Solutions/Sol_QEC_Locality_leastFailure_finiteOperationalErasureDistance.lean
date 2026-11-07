-- Prove2me | solution 1 for QEC.Locality.leastFailure_finiteOperationalErasureDistance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:24:13.729247+00:00
-- url     : https://prove2.me/submissions/2d6018dd-9d00-4d45-986d-f8418220f736

import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Locality_CorrectableRegions_OperationalErasureDistance

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution
    (C : Semantics.QuantumCode (Semantics.Qubit.QubitRegister ι))
    (hFailure : ∃ n, FiniteOperationalErasureFailureAt C n) :
    FiniteOperationalErasureFailureAt C (finiteOperationalErasureDistance C) ∧
      ∀ n, FiniteOperationalErasureFailureAt C n → finiteOperationalErasureDistance C ≤ n := by
  classical
  rw [finiteOperationalErasureDistance, dif_pos hFailure]
  exact ⟨Nat.find_spec hFailure, fun _ h => Nat.find_min' hFailure h⟩
end QEC.Locality
