-- Prove2me | solution 1 for QEC.Locality.erasureRecoverableFromRegister_of_card_lt_finiteOperationalErasureDistance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:14:09.372864+00:00
-- url     : https://prove2.me/submissions/de361290-1d37-4e18-8474-f0dfcd9390ca

import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Locality_CorrectableRegions_OperationalErasureDistance
import Theorems.Thm_QEC_Locality_nonrecoverableCardLowerBound_finiteOperationalErasureDistance

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
    (hCard : S.selected.card < finiteOperationalErasureDistance C) :
    S.ErasureRecoverableFromRegister C := by
  classical
  by_contra hS
  exact (Nat.not_le_of_lt hCard)
    (nonrecoverableCardLowerBound_finiteOperationalErasureDistance C S hS)
end QEC.Locality
