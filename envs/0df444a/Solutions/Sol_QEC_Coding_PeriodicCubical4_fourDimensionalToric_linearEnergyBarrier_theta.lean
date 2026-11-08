-- Prove2me | solution 1 for QEC.Coding.PeriodicCubical4.fourDimensionalToric_linearEnergyBarrier_theta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:47:23.898484+00:00
-- url     : https://prove2.me/submissions/263b57ce-e072-4a1c-806c-6e9e39a545d8

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_CoordinateSymmetry
import Definitions.Def_QEC_Results_QuantumMemory_FourDimensionalEnergyBarrier
import Theorems.Thm_QEC_Coding_PeriodicCubical4_dualSectorSweepPath_hasDualSectorEndpoint
import Theorems.Thm_QEC_Coding_PeriodicCubical4_half_le_pathHeight_of_hasDualSectorEndpoint
import Theorems.Thm_QEC_Coding_PeriodicCubical4_half_le_pathHeight_of_hasPrimalSectorEndpoint
import Theorems.Thm_QEC_Coding_PeriodicCubical4_pathHeight_dualSectorSweepPath_le
import Theorems.Thm_QEC_Coding_PeriodicCubical4_pathHeight_primalSectorSweepPath_le
import Theorems.Thm_QEC_Coding_PeriodicCubical4_primalSectorSweepPath_hasPrimalSectorEndpoint


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
variable {L : Nat} [NeZero L] [Fact (1 < L)]
namespace QEC.Coding.PeriodicCubical4
theorem _root_.solution :
    (∀ (s : MembraneSector) (γ : PauliErrorPath (ι := Plaquette L)),
      HasPrimalSectorEndpoint γ s →
        L / 2 ≤ (toricHamiltonian (L := L)).pathHeight γ) ∧
    (∀ (s : MembraneSector) (γ : PauliErrorPath (ι := Plaquette L)),
      HasDualSectorEndpoint γ s →
        L / 2 ≤ (toricHamiltonian (L := L)).pathHeight γ) ∧
    (∀ s : MembraneSector,
      HasPrimalSectorEndpoint (primalSectorSweepPath (L := L) s) s ∧
        (toricHamiltonian (L := L)).pathHeight
          (primalSectorSweepPath (L := L) s) ≤ 384 * L) ∧
    (∀ s : MembraneSector,
      HasDualSectorEndpoint (dualSectorSweepPath (L := L) s) s ∧
        (toricHamiltonian (L := L)).pathHeight
          (dualSectorSweepPath (L := L) s) ≤ 384 * L) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s gamma hgamma
    exact half_le_pathHeight_of_hasPrimalSectorEndpoint gamma s hgamma
  · intro s gamma hgamma
    exact half_le_pathHeight_of_hasDualSectorEndpoint gamma s hgamma
  · intro s
    exact ⟨primalSectorSweepPath_hasPrimalSectorEndpoint s,
      pathHeight_primalSectorSweepPath_le s⟩
  · intro s
    exact ⟨dualSectorSweepPath_hasDualSectorEndpoint s,
      pathHeight_dualSectorSweepPath_le s⟩
end QEC.Coding.PeriodicCubical4
