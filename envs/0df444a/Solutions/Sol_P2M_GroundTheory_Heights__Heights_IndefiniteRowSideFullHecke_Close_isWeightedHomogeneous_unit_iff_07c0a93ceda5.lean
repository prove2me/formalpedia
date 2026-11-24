-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_isWeightedHomogeneous_unit_iff_07c0a93ceda5
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:07.3747+00:00
-- url     : https://prove2.me/submissions/4c2e698b-2946-463d-a191-1ee992f2f35c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_OneBlockIdealEqComapProjIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_RenameBlockIsWeightedHomogeneous
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_weight_one_eq_sum_351aebacb5b4

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
theorem _root_.solution {r m : ℕ} (f : MvPolynomial (Coord (fun _ : Unit ↦ r)) ℤ) :
    IsWeightedHomogeneous (coordDeg (fun _ : Unit ↦ r)) f (fun _ ↦ m) ↔ f.IsHomogeneous m := by
  have hw : ∀ d : Coord (fun _ : Unit ↦ r) →₀ ℕ,
      Finsupp.weight (coordDeg (fun _ : Unit ↦ r)) d = fun _ ↦ Finsupp.weight 1 d := by
    intro d
    funext u
    rw [weight_one_eq_sum, Fintype.sum_unique]
  constructor
  · intro h d hd
    exact congr_fun ((hw d).symm.trans (h hd)) ()
  · intro h d hd
    rw [hw d, h hd]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
