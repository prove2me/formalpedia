-- Prove2me | solution 1 for QEC.Semantics.Qubit.localXSupport_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:08:30.021476+00:00
-- url     : https://prove2.me/submissions/dcc783ae-5e8e-4175-8ec9-17987df75f48

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
namespace QEC.Semantics.Qubit
theorem _root_.solution (s : Finset ι)
    (ψ : QubitRegister ι) (bits : Bitstring ι) :
    localXSupport s ψ bits = ψ (flipSupport s bits) :=
  rfl
end QEC.Semantics.Qubit
