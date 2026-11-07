-- Prove2me | solution 1 for QEC.Coding.PeriodicCubical4.toricGenerator_mem_binaryCSSCheckSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T03:31:19.471951+00:00
-- url     : https://prove2.me/submissions/9e977f1f-ab98-475b-8641-324fca77b986

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Hamiltonian
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_LogicalSectors

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic
namespace QEC.Coding.PeriodicCubical4
theorem _root_.solution {L : Nat} [NeZero L] [Fact (1 < L)]
    (j : Sum (Link L) (Cube L)) :
    toricGenerator (L := L) j ∈ binaryCSSCheckSet
      (plaquetteChainComplex (L := L)).firstCoboundaryCheckCode
      (plaquetteChainComplex (L := L)).middleBoundaryCode := by
  cases j with
  | inl e =>
      rw [toricGenerator_inl]
      exact Or.inl ⟨wordLinearMapTranspose boundary2 (Pi.single e 1),
        ((plaquetteChainComplex (L := L)).mem_firstCoboundaryCheckCode_iff _).2
          ⟨Pi.single e 1, rfl⟩, rfl⟩
  | inr c =>
      rw [toricGenerator_inr]
      exact Or.inr ⟨boundary3 (Pi.single c 1),
        ((plaquetteChainComplex (L := L)).mem_middleBoundaryCode_iff _).2
          ⟨Pi.single c 1, rfl⟩, rfl⟩
end QEC.Coding.PeriodicCubical4
