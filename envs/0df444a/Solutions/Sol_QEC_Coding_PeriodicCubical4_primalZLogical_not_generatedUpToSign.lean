-- Prove2me | solution 1 for QEC.Coding.PeriodicCubical4.primalZLogical_not_generatedUpToSign
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:44:38.480518+00:00
-- url     : https://prove2.me/submissions/95b0b7c1-70a5-499f-bf23-6fe15b0c2832

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Hamiltonian
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_LogicalSectors
import Theorems.Thm_QEC_Coding_PeriodicCubical4_primalXYMembrane_not_mem_middleBoundaryCode
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
      (toricGenerator (L := L)) (primalZLogical z₀ w₀) := by
  rintro ⟨S, hgenerated, hvector⟩
  have hcomponents := generatedStabilizer_css_components
    (plaquetteChainComplex (L := L)).firstCoboundaryCheckCode
    (plaquetteChainComplex (L := L)).middleBoundaryCode
    (plaquetteChainComplex (L := L)).middleBoundaryCode_le_firstCoboundaryCheckCode_dual
    (toricGenerator (L := L)) toricGenerator_mem_binaryCSSCheckSet hgenerated
  have hz : primalXYMembrane z₀ w₀ = S.vector.zPart :=
    congrArg (fun v => v.zPart) hvector
  exact primalXYMembrane_not_mem_middleBoundaryCode x₀ y₀ z₀ w₀ (by
    rw [hz]
    exact hcomponents.2.2)
end QEC.Coding.PeriodicCubical4
