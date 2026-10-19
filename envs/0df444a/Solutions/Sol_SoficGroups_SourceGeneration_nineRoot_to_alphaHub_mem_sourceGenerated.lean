-- Prove2me | solution 1 for SoficGroups.SourceGeneration.nineRoot_to_alphaHub_mem_sourceGenerated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:51.68578+00:00
-- url     : https://prove2.me/submissions/907d1c23-abdb-46a9-a923-3e1d65609f3e

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_SourceGeneration_alphaBetaRoot_mem_sourceGenerated
import Theorems.Thm_SoficGroups_SourceGeneration_prefixElementaryUnit_mem_of_two_step
import Theorems.Thm_SoficGroups_SourceGeneration_alphaNuRoot_mem_sourceGenerated

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
open SoficGroups.SourceGeneration
open scoped commutatorElement
namespace SoficGroups.SourceGeneration
theorem _root_.solution
    (i : Fin 9) (hi : i ≠ 0) (a : BinaryLeavitt) :
    prefixElementaryUnit ninePrefixCode i 0 hi a ∈ sourceGeneratedGroup := by
  fin_cases i
  · exact (hi rfl).elim
  · exact prefixElementaryUnit_mem_of_two_step
      ninePrefixCode sourceGeneratedGroup 1 3 0
      (by decide) (by decide) hi a
      (by
        simpa [alphaBetaNineIndex] using
          alphaBetaRoot_mem_sourceGenerated
            (0 : Fin 3) (1 : Fin 3) (by decide)
            (1 : Fin 2) (0 : Fin 2) a)
      (by
        simpa [alphaBetaNineIndex] using
          alphaBetaRoot_mem_sourceGenerated
            (1 : Fin 3) (0 : Fin 3) (by decide)
            (0 : Fin 2) (0 : Fin 2) (1 : BinaryLeavitt))
  · exact prefixElementaryUnit_mem_of_two_step
      ninePrefixCode sourceGeneratedGroup 2 3 0
      (by decide) (by decide) hi a
      (by
        simpa [alphaNuNineIndex] using
          alphaNuRoot_mem_sourceGenerated
            (0 : Fin 3) (1 : Fin 3) (by decide)
            (1 : Fin 2) (0 : Fin 2) a)
      (by
        simpa [alphaBetaNineIndex] using
          alphaBetaRoot_mem_sourceGenerated
            (1 : Fin 3) (0 : Fin 3) (by decide)
            (0 : Fin 2) (0 : Fin 2) (1 : BinaryLeavitt))
  · simpa [alphaBetaNineIndex] using
      alphaBetaRoot_mem_sourceGenerated
        (1 : Fin 3) (0 : Fin 3) (by decide)
        (0 : Fin 2) (0 : Fin 2) a
  · simpa [alphaBetaNineIndex] using
      alphaBetaRoot_mem_sourceGenerated
        (1 : Fin 3) (0 : Fin 3) (by decide)
        (1 : Fin 2) (0 : Fin 2) a
  · simpa [alphaNuNineIndex] using
      alphaNuRoot_mem_sourceGenerated
        (1 : Fin 3) (0 : Fin 3) (by decide)
        (1 : Fin 2) (0 : Fin 2) a
  · simpa [alphaBetaNineIndex] using
      alphaBetaRoot_mem_sourceGenerated
        (2 : Fin 3) (0 : Fin 3) (by decide)
        (0 : Fin 2) (0 : Fin 2) a
  · simpa [alphaBetaNineIndex] using
      alphaBetaRoot_mem_sourceGenerated
        (2 : Fin 3) (0 : Fin 3) (by decide)
        (1 : Fin 2) (0 : Fin 2) a
  · simpa [alphaNuNineIndex] using
      alphaNuRoot_mem_sourceGenerated
        (2 : Fin 3) (0 : Fin 3) (by decide)
        (1 : Fin 2) (0 : Fin 2) a
end SoficGroups.SourceGeneration
