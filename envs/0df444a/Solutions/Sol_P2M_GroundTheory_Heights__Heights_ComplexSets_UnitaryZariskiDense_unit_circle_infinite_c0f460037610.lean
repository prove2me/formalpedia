-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_UnitaryZariskiDense_unit_circle_infinite_c0f460037610
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:22:32.986706+00:00
-- url     : https://prove2.me/submissions/8ff4c1fa-8e1b-4dc3-a910-a26961cf0101

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StUnitaryZariskiDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PUnitaryZariskiDense

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial Matrix Complex
noncomputable section
open GroundTheory.Heights₂.Heights.ComplexSets.UnitaryZariskiDense
namespace GroundTheory.Heights₂.Heights.ComplexSets.UnitaryZariskiDense
theorem _root_.solution : {z : ℂ | ‖z‖ = 1}.Infinite := by
  intro hfin
  have hsub : Polynomial.nthRootsFinset (hfin.toFinset.card + 1) (1 : ℂ) ⊆ hfin.toFinset := by
    intro z hz
    rw [Polynomial.mem_nthRootsFinset (Nat.succ_pos _)] at hz
    rw [Set.Finite.mem_toFinset]
    exact Complex.norm_eq_one_of_pow_eq_one hz (Nat.succ_ne_zero _)
  have hc := Finset.card_le_card hsub
  rw [(Complex.isPrimitiveRoot_exp (hfin.toFinset.card + 1) (Nat.succ_ne_zero _)).card_nthRootsFinset]
    at hc
  omega
end GroundTheory.Heights₂.Heights.ComplexSets.UnitaryZariskiDense
