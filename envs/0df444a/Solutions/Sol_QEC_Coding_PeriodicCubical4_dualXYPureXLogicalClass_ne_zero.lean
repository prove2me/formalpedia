-- Prove2me | solution 1 for QEC.Coding.PeriodicCubical4.dualXYPureXLogicalClass_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:34:29.832987+00:00
-- url     : https://prove2.me/submissions/92657c7a-27f0-4e5a-9150-671d5f18c844

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Hamiltonian
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_LogicalSectors
import Theorems.Thm_QEC_Coding_PeriodicCubical4_dualXYMembrane_not_mem_firstCoboundaryCheckCode

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
namespace QEC.Coding.PeriodicCubical4
theorem _root_.solution {L : Nat} [NeZero L]
    (x₀ y₀ z₀ w₀ : ZMod L) :
    dualXYPureXLogicalClass x₀ y₀ ≠ 0 := by
  intro hzero
  have hmem := (Submodule.Quotient.mk_eq_zero _).1 hzero
  exact dualXYMembrane_not_mem_firstCoboundaryCheckCode x₀ y₀ z₀ w₀ hmem
end QEC.Coding.PeriodicCubical4
