-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_sSup_eq_of_upperBounds_eq_56a7107924cc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:56:37.190612+00:00
-- url     : https://prove2.me/submissions/bc87f546-506f-40c5-93de-bb916d922bd2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_OneBlockIdealEqComapProjIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_RenameBlockIsWeightedHomogeneous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (secM sec IsMultiHomog)
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
theorem _root_.solution {s t : Set ℝ} (h : upperBounds s = upperBounds t) :
    sSup s = sSup t := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · have ht : t = ∅ := by
      by_contra ht
      obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr ht
      have hb : x - 1 ∈ upperBounds t := by rw [← h, upperBounds_empty]; trivial
      linarith [hb hx]
    rw [ht]
  · by_cases hb : BddAbove s
    · have ht : t.Nonempty := by
        by_contra ht
        rw [Set.not_nonempty_iff_eq_empty] at ht
        obtain ⟨x, hx⟩ := hs
        have hb' : x - 1 ∈ upperBounds s := by rw [h, ht, upperBounds_empty]; trivial
        linarith [hb' hx]
      have hbt : BddAbove t := by rw [BddAbove, ← h]; exact hb
      have h1 : IsLeast (upperBounds s) (sSup s) := isLUB_csSup hs hb
      have h2 : IsLeast (upperBounds t) (sSup t) := isLUB_csSup ht hbt
      rw [h] at h1
      exact h1.unique h2
    · have hbt : ¬ BddAbove t := by rwa [BddAbove, ← h]
      rw [Real.sSup_of_not_bddAbove hb, Real.sSup_of_not_bddAbove hbt]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
