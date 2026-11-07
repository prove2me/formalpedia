-- Prove2me | solution 1 for QEC.Coding.PeriodicCubical4.dualXLogical_not_generatedUpToSign
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:45:41.32982+00:00
-- url     : https://prove2.me/submissions/b6d2be3e-1d0c-4aa8-a87f-97706893508f

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Hamiltonian
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_LogicalSectors
import Theorems.Thm_QEC_Coding_PeriodicCubical4_dualXYMembrane_not_mem_firstCoboundaryCheckCode
import Theorems.Thm_QEC_Coding_PeriodicCubical4_toricGenerator_mem_binaryCSSCheckSet
import Theorems.Thm_QEC_Coding_PauliSymplectic_generatedStabilizer_css_components


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic
namespace QEC.Coding.PeriodicCubical4
theorem _root_.solution
    {L : Nat} [NeZero L] [Fact (1 < L)]
    (x₀ y₀ z₀ w₀ : ZMod L) :
    ¬ InGeneratedStabilizerUpToSign
      (toricGenerator (L := L)) (dualXLogical x₀ y₀) := by
  rintro ⟨S, hgenerated, hvector⟩
  have hcomponents := generatedStabilizer_css_components
    (plaquetteChainComplex (L := L)).firstCoboundaryCheckCode
    (plaquetteChainComplex (L := L)).middleBoundaryCode
    (plaquetteChainComplex (L := L)).middleBoundaryCode_le_firstCoboundaryCheckCode_dual
    (toricGenerator (L := L)) toricGenerator_mem_binaryCSSCheckSet hgenerated
  have hx : dualXYMembrane x₀ y₀ = S.vector.xPart :=
    congrArg (fun v => v.xPart) hvector
  exact dualXYMembrane_not_mem_firstCoboundaryCheckCode x₀ y₀ z₀ w₀ (by
    rw [hx]
    exact hcomponents.2.1)
end QEC.Coding.PeriodicCubical4
