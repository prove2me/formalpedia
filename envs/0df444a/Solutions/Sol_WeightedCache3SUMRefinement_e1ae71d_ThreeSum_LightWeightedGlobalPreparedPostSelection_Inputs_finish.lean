-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalPreparedPostSelection.Inputs.finish
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T12:57:39.961055+00:00
-- url     : https://prove2.me/submissions/69934c29-181b-415e-abce-2cebeec1f02a

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_LightTernaryFinalPreparation
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPostSelectionClosed
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPreparedPostSelection

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalPreparedPostSelection
open Light LightSubsetAddress LightOriginalSurvivorPair LightOriginalCollisionCleanup
set_option maxHeartbeats 4000000
set_option maxRecDepth 24000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalPreparedPostSelection
namespace Inputs
theorem _root_.solution {c : Layout} {lim : Limits} {d U W : ℕ} {μ ν : ℕ → ℤ}
    {A B C : ℕ → ℤ} {keysB keysC : ℕ → ℕ}
    (S : Inputs c lim d U W μ A B C keysB keysC)
    (hpowers : Powers ν c.powers W)
    (hcB : ∀ k < c.q, ν (c.histB+k) = (LightHistogram.count keysB k c.nB : ℤ))
    (hcC : ∀ k < c.q, ν (c.histC+k) = (LightHistogram.count keysC k c.nC : ℤ))
    (hkeep : Kept μ ν c.powers) : Resources c lim d U W ν A B C keysB keysC := by
  exact {
    hw := S.hw
    hA := S.hA
    hB := S.hB
    hC := S.hC
    hkB := S.hkB
    hkC := S.hkC
    hhB := S.hhB
    hhC := S.hhC
    hp := S.hp
    hB1 := S.hB1
    hB2 := S.hB2
    hB3 := S.hB3
    hBC := S.hBC
    hC1 := S.hC1
    hC2 := S.hC2
    hC3 := S.hC3
    hEnd := S.hEnd
    hword := S.hword
    hkeysB := S.hkeysB
    hkeysC := S.hkeysC
    hreadKB := fun i hi => (hkeep _ (by have := S.beforeKeyB; omega)).trans (S.hreadKB i hi)
    hreadKC := fun i hi => (hkeep _ (by have := S.beforeKeyC; omega)).trans (S.hreadKC i hi)
    hboundA := S.hboundA
    hboundB := S.hboundB
    hboundC := S.hboundC
    hreadA := fun i hi => (hkeep _ (by have := S.beforeA; omega)).trans (S.hreadA i hi)
    hreadB := fun i hi => (hkeep _ (by have := S.beforeB; omega)).trans (S.hreadB i hi)
    hreadC := fun i hi => (hkeep _ (by have := S.beforeC; omega)).trans (S.hreadC i hi)
    hvalueWord := S.hvalueWord
    hsortedB := S.hsortedB
    hsortedC := S.hsortedC
    hL := S.hL
    hnB := S.hnB
    hnC := S.hnC
    hd := S.hd
    hcountsB := hcB
    hcountsC := hcC
    hpowers := hpowers }
end Inputs
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalPreparedPostSelection
