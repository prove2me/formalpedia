-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_upperBounds_eq_of_sSup_eq_1bfc466c0f85
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:56:38.894855+00:00
-- url     : https://prove2.me/submissions/ff5df7e8-c5e8-4a3e-842b-a9b679e69a9a

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
theorem _root_.solution {s t : Set ℝ} (hs : BddAbove s) (ht : BddAbove t)
    (hne : s.Nonempty ↔ t.Nonempty) (h : sSup s = sSup t) : upperBounds s = upperBounds t := by
  rcases s.eq_empty_or_nonempty with rfl | hs'
  · have : t = ∅ := Set.not_nonempty_iff_eq_empty.mp fun h' ↦ Set.not_nonempty_empty (hne.mpr h')
    rw [this]
  · have ht' := hne.mp hs'
    ext B
    rw [mem_upperBounds, mem_upperBounds, ← csSup_le_iff hs hs', ← csSup_le_iff ht ht', h]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
