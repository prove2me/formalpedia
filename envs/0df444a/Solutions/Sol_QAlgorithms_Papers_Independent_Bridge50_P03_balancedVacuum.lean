-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Bridge50.P03.balancedVacuum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T12:57:53.179646+00:00
-- url     : https://prove2.me/submissions/c2548246-8148-498b-9e08-1bd8c5e68d53

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P03
noncomputable section

open QAlgorithms.Papers.Independent.Bridge50.P03

theorem solution (eta omega : ℝ)
    (heta0 : 0 ≤ eta) (heta1 : eta < 1) (homega : 1 ≤ omega) :
    signedDetectorRate eta omega (1 / 2) 1 =
      balancedVacuumCurve eta omega := by
  have he : 0 < 1 - eta := by linarith
  have ho : 0 < omega := by linarith
  have hs : 0 < omega + 1 - eta := by linarith
  have hq : 0 < (1 - eta) * omega + 1 := by positivity
  have hA : ((1 / 2) * omega + (1 - 1 / 2) * (1 - eta) * 1) /
        ((1 - eta) * ((1 / 2) * (1 - eta) * omega + (1 - 1 / 2) * 1)) =
      (omega + 1 - eta) / ((1 - eta) * ((1 - eta) * omega + 1)) := by
    field_simp
    ring
  have hB : (omega * ((1 / 2) + (1 - eta) * (1 - 1 / 2) * omega * 1)) /
        ((1 / 2) * omega + (1 - eta) * (1 - 1 / 2) * 1) =
      (omega * (1 + (1 - eta) * omega)) / (omega + 1 - eta) := by
    field_simp
    ring
  unfold signedDetectorRate balancedVacuumCurve
  rw [if_neg (by norm_num), hA, hB]

end
