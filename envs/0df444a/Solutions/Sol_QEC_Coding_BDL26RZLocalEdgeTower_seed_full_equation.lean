-- Prove2me | solution 1 for QEC.Coding.BDL26RZLocalEdgeTower.seed_full_equation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:24:43.175794+00:00
-- url     : https://prove2.me/submissions/67508cc3-d565-4c1e-9cc6-5670446e5af4

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroQVertexTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundaryTailInvariance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RZLocalEdgeTower
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_binary_add_eq_zero_iff
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

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
private theorem eq_of_add_zero {I : Type} (a b : Word F I) (h : a+b=0) : a=b := by
  funext r
  exact (binary_add_eq_zero_iff _ _).mp (congrFun h r)
end FixedTotal
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
variable (S : OddScale) (n : Nat) (sigma tau : TopInput S n)
namespace QEC.Coding.BDL26RZLocalEdgeTower
theorem _root_.solution (S : OddScale) (n : Nat) (sigma tau : TopInput S n)
    (i : StepIndex n) (ho : ¬(i.val+2)%2=0)
    (w : LocalizedWord S n sigma tau i.succ)
    (z : (state S (i.val+2)).presentation.Z)
    (e : ZDoubleCylinderEdge (state S (i.val+2)).presentation z S)
    (hw : hammingSupport w.word ⊆ {rzLocalEdge S (i.val+2) ho z e}) :
    (step S n sigma tau i w).lower.word=0 ∧
      w.word+(actualOutput S n sigma i).correction+(actualOutput S n tau i).correction=
        (SuffixData S n).family.coboundary0 i.succ (step S n sigma tau i w).potential := by
  have hz := seed_step_zero S n sigma tau i ho w z e hw
  refine ⟨hz,?_⟩
  have he := (step S n sigma tau i w).equation
  rw [hz,map_zero] at he
  exact eq_of_add_zero _ _ he.symm
end QEC.Coding.BDL26RZLocalEdgeTower
