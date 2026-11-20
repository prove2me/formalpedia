-- Prove2me | solution 1 for QEC.Coding.BDL26RZLocalEdgeTower.snapshot_zero_below
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:34:30.198103+00:00
-- url     : https://prove2.me/submissions/113ca9bc-755c-4391-9167-feaab214dd54

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroQVertexTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundaryTailInvariance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RZLocalEdgeTower
import Theorems.Thm_QEC_Coding_BDL26RZLocalEdgeTower_step_zero
import Theorems.Thm_QEC_Coding_BDL26LocalizedHistoryErrorDescent_path_step

section
noncomputable section
namespace QEC.Coding.BDL26RZLocalEdgeTower
open MultiscaleDecoder BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26LocalizedHistoryErrorDescent BDL26RZMap1CoordinateBridge
open BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26CSSHamiltonian BDL26ActualFailureReadout BDL26TransposedStoppedDecoder
open PauliSymplectic
open scoped Classical BigOperators
section FixedTotal
variable (S : OddScale) (n : Nat) (sigma tau : TopInput S n)
end FixedTotal
private theorem path_zero_below_nat (S : OddScale) (n : Nat) (sigma tau : TopInput S n)
    (top : LocalizedWord S n sigma tau (TopIndex n)) (a : Nat) (ha : a ≤ n)
    (hz : (path S n sigma tau top ⟨a,Nat.lt_succ_of_le ha⟩).word=0)
    (b : LevelIndex n) (hb : b.val ≤ a) : (path S n sigma tau top b).word=0 := by
  cases a with
  | zero =>
      have h : b=⟨0,Nat.lt_succ_of_le ha⟩ := Fin.ext (by change b.val=0; omega)
      subst b
      exact hz
  | succ a =>
      by_cases h : b.val=a+1
      · have h' : b=⟨a+1,Nat.lt_succ_of_le ha⟩ := Fin.ext h
        subst b
        exact hz
      · let i : StepIndex n := ⟨a,by omega⟩
        have hl : (path S n sigma tau top i.castSucc).word=0 := by
          rw [path_step S n sigma tau top i]
          exact step_zero S n sigma tau i _ hz
        exact path_zero_below_nat S n sigma tau top a (by omega) hl b (by omega)
termination_by a
open QEC.Semantics BDL26PairedDecoderPhase
end QEC.Coding.BDL26RZLocalEdgeTower
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RZLocalEdgeTower
open MultiscaleDecoder BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26LocalizedHistoryErrorDescent BDL26RZMap1CoordinateBridge
open BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26CSSHamiltonian BDL26ActualFailureReadout BDL26TransposedStoppedDecoder
open PauliSymplectic
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RZLocalEdgeTower
theorem _root_.solution (S : OddScale) (n : Nat) (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Killed S n q) (b : LevelIndex n)
    (hb : b.val ≤ seedDepth t) :
    (BDL26BoundaryTailInvariance.snapshot S n u q b).word=0 :=
  path_zero_below_nat S n (input S n u)
    (perturbTop S n (input S n u) (BDL26ActualFailureReadout.flip S n q))
    (BDL26BoundaryTailInvariance.physicalTop S n u q) (seedDepth t)
    (by have h:=seedDepth_lt t; omega) (seed_snapshot_zero S n u q t) b hb
end QEC.Coding.BDL26RZLocalEdgeTower
