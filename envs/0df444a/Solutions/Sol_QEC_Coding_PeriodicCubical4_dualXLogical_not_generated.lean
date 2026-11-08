-- Prove2me | solution 1 for QEC.Coding.PeriodicCubical4.dualXLogical_not_generated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:34:37.520269+00:00
-- url     : https://prove2.me/submissions/9f3b6725-6ee6-4be2-aa7d-1f548644a9a1

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Hamiltonian
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_LogicalSectors
import Theorems.Thm_QEC_Coding_PeriodicCubical4_dualXLogical_not_generatedUpToSign

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic
namespace QEC.Coding.PeriodicCubical4
theorem _root_.solution {L : Nat} [NeZero L] [Fact (1 < L)]
    (x₀ y₀ z₀ w₀ : ZMod L) :
    ¬ GeneratedStabilizer (toricGenerator (L := L)) (dualXLogical x₀ y₀) := by
  intro hgenerated
  exact dualXLogical_not_generatedUpToSign x₀ y₀ z₀ w₀
    ⟨dualXLogical x₀ y₀, hgenerated, rfl⟩
end QEC.Coding.PeriodicCubical4
