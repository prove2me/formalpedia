-- Prove2me | solution 2 for QEC.Semantics.Qubit.pauliX_pauliZ_sameSite_anticommute
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T18:46:33.570935+00:00
-- url     : https://prove2.me/submissions/92e9a370-0894-4168-b6c4-1c4291302d54

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

theorem solution :
    pauliX * pauliZ = -(pauliZ * pauliX) := by
  ext ψ b
  simp
