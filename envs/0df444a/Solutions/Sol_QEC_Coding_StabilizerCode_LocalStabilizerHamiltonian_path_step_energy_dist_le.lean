-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.path_step_energy_dist_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:57:02.142919+00:00
-- url     : https://prove2.me/submissions/892f22a0-d854-40cf-bd08-ec244d506d20

import Definitions.Def_QEC_Coding_Stabilizer_Energy
import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_btExcessEnergy_dist_binaryMul_le
import Theorems.Thm_QEC_Coding_PauliErrorPath_getElem_weight_le_one
import Theorems.Thm_QEC_Coding_PauliErrorPath_stateAt_succ


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
    (hn : n < γ.increments.length) :
    Nat.dist (H.btExcessEnergy (γ.stateAt (n + 1)))
        (H.btExcessEnergy (γ.stateAt n)) ≤
      2 * H.participationBound := by
  rw [γ.stateAt_succ n hn]
  exact H.btExcessEnergy_dist_binaryMul_le _ _
    (γ.getElem_weight_le_one n hn)
end QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
