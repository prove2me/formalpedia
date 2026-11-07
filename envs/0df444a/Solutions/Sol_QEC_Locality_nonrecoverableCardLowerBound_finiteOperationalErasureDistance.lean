-- Prove2me | solution 1 for QEC.Locality.nonrecoverableCardLowerBound_finiteOperationalErasureDistance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:12:24.955213+00:00
-- url     : https://prove2.me/submissions/9d9ac5c5-429b-4c20-9426-290ad80589a7

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
    (S : Semantics.FiniteSubsystem ι)
    (hS : ¬ S.ErasureRecoverableFromRegister C) :
    finiteOperationalErasureDistance C ≤ S.selected.card := by
  classical
  have hFailure : ∃ n, FiniteOperationalErasureFailureAt C n :=
    ⟨S.selected.card, S, rfl, hS⟩
  rw [finiteOperationalErasureDistance, dif_pos hFailure]
  exact Nat.find_min' hFailure ⟨S, rfl, hS⟩
end QEC.Locality
