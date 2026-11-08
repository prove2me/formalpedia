-- Prove2me | solution 1 for QEC.Coding.PeriodicCubical4.primalXYPureZLogicalClass_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:34:21.303198+00:00
-- url     : https://prove2.me/submissions/6f4bb9c2-f8cf-4053-b2f7-e7c5ed870908

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Hamiltonian
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_LogicalSectors
import Theorems.Thm_QEC_Coding_PeriodicCubical4_primalXYMembrane_not_mem_middleBoundaryCode

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
namespace QEC.Coding.PeriodicCubical4
theorem _root_.solution {L : Nat} [NeZero L]
    (x₀ y₀ z₀ w₀ : ZMod L) :
    primalXYPureZLogicalClass z₀ w₀ ≠ 0 := by
  intro hzero
  have hmem := (Submodule.Quotient.mk_eq_zero _).1 hzero
  exact primalXYMembrane_not_mem_middleBoundaryCode x₀ y₀ z₀ w₀ hmem
end QEC.Coding.PeriodicCubical4
