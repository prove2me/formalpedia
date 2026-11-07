-- Prove2me | solution 1 for QEC.Coding.PeriodicCubical4.BinarySquare.exists_eq_of_nat_walk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T03:33:32.874596+00:00
-- url     : https://prove2.me/submissions/8c5ce6ca-907f-40c5-a174-19ef698b2543

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic
open QEC.Coding.PeriodicCubical4.BinarySquare
namespace QEC.Coding.PeriodicCubical4.BinarySquare
theorem _root_.solution
    (a : Nat → Nat) (N target : Nat)
    (hstart : a 0 ≤ target) (hend : target ≤ a N)
    (hstep : ∀ k < N, Nat.dist (a (k + 1)) (a k) ≤ 1) :
    ∃ k ≤ N, a k = target := by
  induction N with
  | zero =>
      exact ⟨0, le_rfl, by omega⟩
  | succ N ih =>
      by_cases hbefore : target ≤ a N
      · obtain ⟨k, hk, hktarget⟩ := ih hbefore (fun k hk => hstep k (by omega))
        exact ⟨k, by omega, hktarget⟩
      · refine ⟨N + 1, by omega, ?_⟩
        have hlast := hstep N (by omega)
        unfold Nat.dist at hlast
        omega
end QEC.Coding.PeriodicCubical4.BinarySquare
