-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryErrorTelescoping.source_even_two_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:36:43.190227+00:00
-- url     : https://prove2.me/submissions/9acc863b-2f97-40fb-8f8d-b1120fd8eed3

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_actual_two_run

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryErrorTelescoping
open MultiscaleDecoder BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open scoped Classical
universe u v w
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26HistoryErrorTelescoping
theorem _root_.solution (k : Nat) (hk : 1 ≤ k)
    (sigma : (indexedFamily S (2*k)).Syndrome (TopIndex (2*k)))
    (e : (indexedFamily S (2*k)).Cochain1 (TopIndex (2*k))) :
    let m := 2*(k-1)
    let s := sourceEvenInput S k hk sigma
    let v := sourceEvenError S k hk e
    ∃ (h : (SuffixData S m).family.Cochain1 0)
      (R : (SuffixData S m).family.Cochain0 (TopIndex m)),
      (SuffixData S m).family.coboundary1 0 h =
        actualReadout S m s 0 + actualReadout S m (perturbTop S m s v) 0 ∧
      v + historyLiftedCorrection (SuffixData S m) (actualHistory S m s) +
          historyLiftedCorrection (SuffixData S m) (actualHistory S m (perturbTop S m s v)) =
        intervalMap1 (SuffixData S m) 0 (TopIndex m) (Nat.zero_le _)
          (h + (actualBase S m).decode (actualInputs S m s 0) +
            (actualBase S m).decode (actualInputs S m (perturbTop S m s v) 0)) +
          (SuffixData S m).family.coboundary0 (TopIndex m) R ∧
      (SuffixData S m).family.coboundary1 (TopIndex m)
        ((SuffixData S m).family.coboundary0 (TopIndex m) R) = 0 ∧
      (SuffixData S m).family.coboundary1 0
        (h + (actualBase S m).decode (actualInputs S m s 0) +
          (actualBase S m).decode (actualInputs S m (perturbTop S m s v) 0)) = 0 ∧
      (SuffixData S m).family.coboundary1 (TopIndex m)
        (v + historyLiftedCorrection (SuffixData S m) (actualHistory S m s) +
          historyLiftedCorrection (SuffixData S m) (actualHistory S m (perturbTop S m s v))) = 0 := by
  cases k with
  | zero => omega
  | succ k => exact actual_two_run S (2*k) sigma e
end QEC.Coding.BDL26HistoryErrorTelescoping
