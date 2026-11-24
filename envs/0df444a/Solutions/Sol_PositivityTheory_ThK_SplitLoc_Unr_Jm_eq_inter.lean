-- Prove2me | solution 1 for PositivityTheory.ThK.SplitLoc.Unr.Jm_eq_inter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:15:44.072955+00:00
-- url     : https://prove2.me/submissions/33e33529-9fa6-44b6-86e3-ace2ec5f87fa

import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SplitLoc
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyDeepSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_UpperProjectionInverseTransposeRightInverse

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open PositivityTheory PositivityTheory.ThK PositivityTheory.ThK.SplitLoc PositivityTheory.ThK.SplitLoc.Unr
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.SmGL
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [MeasurableSpace k] [BorelSpace k]
open GlobalTheory.SatakeBound
namespace PositivityTheory.ThK.SplitLoc.Unr
theorem _root_.solution {n : ℕ} {φ : Matrix (Fin n) (Fin n) k → ℂ} (hs : ∀ x, φ x ≠ 0 → ∀ i j, x i j ∈ 𝒪[k]) (m : ℤ) :
    Jm n φ m = ∫ g in dShell n m ∩ {g | ∀ i j, g.val i j ∈ 𝒪[k]}, φ g.val ∂haarVol (KO k (Fin n)) := by
  have ho : IsOpen {g : GL (Fin n) k | ∀ i j, g.val i j ∈ 𝒪[k]} :=
    (isOpen_intMatrix (k := k) (m := Fin n) (n := Fin n)).preimage (Units.continuous_val (M := Matrix (Fin n) (Fin n) k))
  rw [← setIntegral_indicator ho.measurableSet, Jm]
  congr 1
  exact (Set.indicator_eq_self.2 fun g hg => hs _ hg).symm
end PositivityTheory.ThK.SplitLoc.Unr
