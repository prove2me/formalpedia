-- Prove2me | solution 1 for QEC.Semantics.Qubit.localXSupport_localZSupport_apply
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T17:53:56.258891+00:00
-- url     : https://prove2.me/submissions/cf0265b2-fa86-4231-b2b0-aef800472862

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
    (localXSupport xSupport * localZSupport zSupport) ψ bits =
      zSupportPhase zSupport (flipSupport xSupport bits) *
        ψ (flipSupport xSupport bits) := by
  solve | rfl | simp [Bitstring, QubitRegister, flipSupport, zSupportPhase, localXSupport, localZSupport] | simp_all [Bitstring, QubitRegister, flipSupport, zSupportPhase, localXSupport, localZSupport] | omega | norm_num
