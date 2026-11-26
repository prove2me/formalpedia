-- Prove2me | solution 1 for TunnellMap.RecordDA.canonicalResidualMap_inverseByRerun
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:44:34.140655+00:00
-- url     : https://prove2.me/submissions/f7bb7c54-b082-4ace-8733-aac901744036

import Definitions.Def_TunnellMap_RecordDeferredAcceptanceCorrect
import Definitions.Def_TunnellMap_RecordSign
import Definitions.Def_TunnellMap_InverseByRerun
import Theorems.Thm_TunnellMap_RecordDA_inverseByRerun_apply
import Theorems.Thm_TunnellMap_canonicalEta_mem
import Theorems.Thm_TunnellMap_canonicalResidualMapOf_signAct
import Theorems.Thm_TunnellMap_residualTarget_decomposition
import Theorems.Thm_TunnellMap_targetLiftSign_mem


set_option autoImplicit true
open TunnellMap
open TunnellMap.RecordDA
open OrderedGenerator BlockGen GloballyRanked
variable {n : ℤ}
variable [Fintype (BOddRep n)]
variable [Fintype (ARep n)]
namespace TunnellMap.RecordDA
theorem _root_.solution (hn : Odd n) (hnpos : 0 < n)
    (frames : FrameFamily n)
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit)
    (fallback : BResidual n) (y : AResidual n) :
    canonicalResidualMapOf hnpos (residualOrbitMatching hnpos hcard)
        (inverseByRerun frames fallback y) = y := by
  set M := residualOrbitMatching hnpos hcard with hM
  set o := (aResidualInvolution n hnpos).orbit y with ho
  set q := M.symm o with hqdef
  set rho := targetLiftSign (residualTargetLift y) with hrho
  set eta := canonicalEta hnpos q o with heta
  have hMq : M q = o := Equiv.apply_symm_apply M o
  have hrm : rho = 1 ∨ rho = -1 := targetLiftSign_mem _
  have hem : eta = 1 ∨ eta = -1 := canonicalEta_mem hnpos q o
  have hprod : rho * eta = 1 ∨ rho * eta = -1 := by
    rcases hrm with h | h <;> rcases hem with h' | h' <;> rw [h, h'] <;> norm_num
  have hx : inverseByRerun frames fallback y =
      signActB (rho * eta) (canonicalBResidualRepresentative q) := by
    rw [inverseByRerun_apply hn hnpos frames hcard]
  rw [hx, canonicalResidualMapOf_signAct hnpos M q hprod, hMq, ← heta, mul_assoc]
  have hdec := residualTarget_decomposition hnpos y
  rw [← ho, ← hrho] at hdec
  rcases hem with h | h <;> rw [h] <;> norm_num <;> exact hdec
end TunnellMap.RecordDA
