-- Prove2me | solution 1 for QEC.Semantics.Qubit.localZSupport_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:08:31.834057+00:00
-- url     : https://prove2.me/submissions/0e3c3af0-ee02-4a6f-8859-4d253022b19e

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
    localZSupport s ψ bits = zSupportPhase s bits * ψ bits :=
  rfl
end QEC.Semantics.Qubit
