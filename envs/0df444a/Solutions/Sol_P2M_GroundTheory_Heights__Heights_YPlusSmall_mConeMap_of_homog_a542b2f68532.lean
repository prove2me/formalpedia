-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_YPlusSmall_mConeMap_of_homog_a542b2f68532
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:25:18.589839+00:00
-- url     : https://prove2.me/submissions/e1ce101d-5d0d-405a-98b7-6531a14ace1e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PYPlusSmall
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_YPlusSmall_aeval_blockScale_5c8c7b72759e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_YPlusSmall_aeval_C_comp_c5112b1b05c1

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.YPlusSmall
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights.YPlusSmall
theorem _root_.solution {Ω : Type} [Field Ω] {f : MvPolynomial (Coord n) ℤ} {e : ι → ℕ}
    (hf : Geo.IsMultiHomog (ι := blockIdx n) f e) (y : Coord n → Ω) :
    Geo.mConeMap (ι := blockIdx n) y f = C (aeval y f) * ∏ k, X k ^ e k := by
  show aeval (fun p : Coord n ↦ (C (y p) * X p.1 : MvPolynomial ι Ω)) f = _
  rw [show (fun p : Coord n ↦ (C (y p) * X p.1 : MvPolynomial ι Ω)) = fun p ↦ X p.1 * C (y p) from
    funext fun _ ↦ mul_comm _ _]
  refine (aeval_blockScale hf (fun k ↦ (X k : MvPolynomial ι Ω)) (fun p ↦ C (y p))).trans ?_
  erw [aeval_C_comp]
  rw [mul_comm]
end GroundTheory.Heights₂.Heights.YPlusSmall
