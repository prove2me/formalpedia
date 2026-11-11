-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryLogicalResidual.class_eq_iff_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T11:09:02.445368+00:00
-- url     : https://prove2.me/submissions/cf31908a-60e9-4e1d-8c16-343b63b2ccb8

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LogicalQubitPreservation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual_Intervals

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryLogicalResidual
open MultiscaleDecoder BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge
open scoped Classical
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26HistoryLogicalResidual
theorem _root_.solution (r : Nat) (v w : FC.Cocycle S r) :
    FC.classOf S r v = FC.classOf S r w ↔
      ∃ f : Word BDL26Field (state S r).presentation.X,
        tannerCoboundary0 (state S r).presentation f = v.val-w.val := by
  constructor
  · intro h
    have hb := (Submodule.Quotient.eq
      (BDL26FiniteCohomology.complex S r).middleCoboundaryInCocycles).mp h
    change v.val-w.val ∈ (BDL26FiniteCohomology.complex S r).firstCoboundaryCheckCode.carrier at hb
    exact (BDL26RZCohomology.mem_boundary_iff _ _).mp hb
  · intro h
    apply (Submodule.Quotient.eq
      (BDL26FiniteCohomology.complex S r).middleCoboundaryInCocycles).mpr
    exact (BDL26RZCohomology.mem_boundary_iff _ _).mpr h
end QEC.Coding.BDL26HistoryLogicalResidual
