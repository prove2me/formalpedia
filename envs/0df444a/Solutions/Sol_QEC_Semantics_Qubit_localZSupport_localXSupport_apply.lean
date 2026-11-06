-- Prove2me | solution 1 for QEC.Semantics.Qubit.localZSupport_localXSupport_apply
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T17:54:56.112003+00:00
-- url     : https://prove2.me/submissions/fe7c02ac-2883-42b9-b9fc-683efdfb9eb5

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Core_Qubit
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open QEC.Semantics.Qubit
open Classical
open scoped BigOperators ComplexOrder
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem solution (xSupport zSupport : Finset ι)
    (ψ : QubitRegister ι) (bits : Bitstring ι) :
    (localZSupport zSupport * localXSupport xSupport) ψ bits =
      zSupportPhase zSupport bits * ψ (flipSupport xSupport bits) := by
  solve | rfl | simp [Bitstring, QubitRegister, flipSupport, zSupportPhase, localXSupport, localZSupport] | simp_all [Bitstring, QubitRegister, flipSupport, zSupportPhase, localXSupport, localZSupport] | omega | norm_num
