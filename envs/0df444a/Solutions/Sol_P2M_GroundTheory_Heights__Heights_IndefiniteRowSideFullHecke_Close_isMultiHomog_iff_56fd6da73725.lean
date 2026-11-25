-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_isMultiHomog_iff_56fd6da73725
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:56:17.33238+00:00
-- url     : https://prove2.me/submissions/34dbd86e-25d8-45c6-870e-3e2598e1ca7e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_OneBlockIdealEqComapProjIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_RenameBlockIsWeightedHomogeneous
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_weight_coordDeg_apply_ad5acafbd2e4

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
theorem _root_.solution (f : MvPolynomial (Coord n) ℤ) (a : ι → ℕ) :
    IsMultiHomog (ι := fun k ↦ Fin (n k + 1)) f a ↔ IsWeightedHomogeneous (coordDeg n) f a := by
  constructor
  · intro h d hd
    funext k
    rw [weight_coordDeg_apply]
    exact h d (mem_support_iff.mpr hd) k
  · intro h d hd k
    rw [← weight_coordDeg_apply, h (mem_support_iff.mp hd)]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
