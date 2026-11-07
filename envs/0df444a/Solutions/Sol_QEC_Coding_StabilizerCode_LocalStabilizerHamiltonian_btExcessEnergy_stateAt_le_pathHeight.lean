-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.btExcessEnergy_stateAt_le_pathHeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:27:57.068212+00:00
-- url     : https://prove2.me/submissions/cf7c0ba0-c205-4c09-bb3d-d82512f0d7d1

import Definitions.Def_QEC_Coding_Stabilizer_Energy
import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open PauliSymplectic
open scoped Classical
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
open QEC.Coding.StabilizerCode QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
namespace QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
theorem _root_.solution
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (γ : PauliErrorPath (ι := ι)) (n : Nat)
    (hn : n ≤ γ.increments.length) :
    H.btExcessEnergy (γ.stateAt n) ≤ H.pathHeight γ := by
  rw [pathHeight]
  exact Finset.le_sup (α := Nat)
    (f := fun m => H.btExcessEnergy (γ.stateAt m))
    (Finset.mem_range.mpr (show n < γ.increments.length + 1 by omega))
end QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
