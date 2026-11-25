-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeModel_isWeightedHomogeneous_coordDeg_iff_c2022d0310d2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:02:31.621303+00:00
-- url     : https://prove2.me/submissions/555d91bf-d2ee-4528-8618-9b0d1a4972a8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelA
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_weight_one_eq_degree_27ee5a5b405e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.LatticeModel
variable {K : Type} [Field K] [NumberField K]
variable {m N : ℕ} {L : Submodule (𝓞 K) (Fin m → K)} {φ : Fin (N + 1) → Fin m → K}
variable {R : Type*} [CommSemiring R]
namespace GroundTheory.Heights₂.Heights.LatticeModel
theorem _root_.solution (f : MvPolynomial (Coord fun _ : Unit ↦ N) R) (μ : Unit → ℕ) :
    IsWeightedHomogeneous (coordDeg fun _ : Unit ↦ N) f μ ↔ f.IsHomogeneous (μ ()) := by
  constructor
  · intro h s hs
    have := congrFun (h hs) ()
    rw [weight_coordDeg] at this
    rw [weight_one_eq_degree]
    exact this
  · intro h s hs
    rw [weight_coordDeg]
    funext u
    have := h hs
    rw [weight_one_eq_degree] at this
    exact this
end GroundTheory.Heights₂.Heights.LatticeModel
