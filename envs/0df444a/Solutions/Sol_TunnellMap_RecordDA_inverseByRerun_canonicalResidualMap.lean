-- Prove2me | solution 1 for TunnellMap.RecordDA.inverseByRerun_canonicalResidualMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:44:41.241401+00:00
-- url     : https://prove2.me/submissions/afeb7815-aae9-4e04-bd71-8dd107ea932e

import Definitions.Def_TunnellMap_RecordDeferredAcceptanceCorrect
import Definitions.Def_TunnellMap_RecordSign
import Definitions.Def_TunnellMap_InverseByRerun
import Theorems.Thm_TunnellMap_RecordDA_inverseByRerun_apply
import Theorems.Thm_TunnellMap_FreeInvolution_signAct_inj_sign
import Theorems.Thm_TunnellMap_bResidualSign_mem
import Theorems.Thm_TunnellMap_bResidual_decomposition
import Theorems.Thm_TunnellMap_canonicalEta_mem
import Theorems.Thm_TunnellMap_orbit_canonicalAResidualRepresentative
import Theorems.Thm_TunnellMap_orbit_signActA
import Theorems.Thm_TunnellMap_residualTarget_decomposition
import Theorems.Thm_TunnellMap_targetLiftSign_mem
attribute [local simp] TunnellMap.orbit_canonicalAResidualRepresentative
attribute [local simp] TunnellMap.orbit_signActA



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
    (fallback : BResidual n) (x : BResidual n) :
    inverseByRerun frames fallback
        (canonicalResidualMapOf hnpos (residualOrbitMatching hnpos hcard) x) = x := by
  set M := residualOrbitMatching hnpos hcard with hM
  set q := (bResidualInvolution n).orbit x with hq
  set F := canonicalAResidualRepresentative hnpos (M q) with hF
  set sigma := bResidualSign x with hsigma
  set eta := canonicalEta hnpos q (M q) with heta
  have hsm : sigma = 1 ∨ sigma = -1 := bResidualSign_mem x
  have hem : eta = 1 ∨ eta = -1 := canonicalEta_mem hnpos q (M q)
  have hprod : sigma * eta = 1 ∨ sigma * eta = -1 := by
    rcases hsm with h | h <;> rcases hem with h' | h' <;> rw [h, h'] <;> norm_num
  have hy : canonicalResidualMapOf hnpos M x = signActA hnpos (sigma * eta) F := rfl
  have horb : (aResidualInvolution n hnpos).orbit
      (canonicalResidualMapOf hnpos M x) = M q := by
    rw [hy, orbit_signActA, hF, orbit_canonicalAResidualRepresentative]
  have hrho : targetLiftSign
      (residualTargetLift (canonicalResidualMapOf hnpos M x)) = sigma * eta := by
    refine (aResidualInvolution n hnpos).signAct_inj_sign
      (x := F) (targetLiftSign_mem _) hprod ?_
    have hdec := residualTarget_decomposition hnpos (canonicalResidualMapOf hnpos M x)
    rw [horb, ← hF] at hdec
    show signActA hnpos _ F = signActA hnpos (sigma * eta) F
    rw [hdec, hy]
  rw [inverseByRerun_apply hn hnpos frames hcard, horb, hrho,
    Equiv.symm_apply_apply, ← heta, mul_assoc]
  rcases hem with h | h <;> rw [h] <;> norm_num <;>
    exact bResidual_decomposition x
end TunnellMap.RecordDA
