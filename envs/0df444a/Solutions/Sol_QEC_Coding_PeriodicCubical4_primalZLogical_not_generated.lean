-- Prove2me | solution 1 for QEC.Coding.PeriodicCubical4.primalZLogical_not_generated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:34:32.792417+00:00
-- url     : https://prove2.me/submissions/9bcf409a-bd07-43f4-983f-3c4a7171b82c

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Hamiltonian
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_LogicalSectors
import Theorems.Thm_QEC_Coding_PeriodicCubical4_primalZLogical_not_generatedUpToSign

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic
namespace QEC.Coding.PeriodicCubical4
theorem _root_.solution {L : Nat} [NeZero L] [Fact (1 < L)]
    (x₀ y₀ z₀ w₀ : ZMod L) :
    ¬ GeneratedStabilizer (toricGenerator (L := L)) (primalZLogical z₀ w₀) := by
  intro hgenerated
  exact primalZLogical_not_generatedUpToSign x₀ y₀ z₀ w₀
    ⟨primalZLogical z₀ w₀, hgenerated, rfl⟩
end QEC.Coding.PeriodicCubical4
