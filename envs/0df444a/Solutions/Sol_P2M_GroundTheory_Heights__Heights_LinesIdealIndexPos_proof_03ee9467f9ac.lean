-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LinesIdealIndexPos_proof_03ee9467f9ac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:36:55.059792+00:00
-- url     : https://prove2.me/submissions/926039ac-7a01-4592-9947-e7803428d7d9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesIdealIndexPos
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesIdealIndexPos_toOne_injective_1a42c0d39bbb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesIdealIndexPos_fg_and_span_c3c03cd61257

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
open NumberField
open scoped nonZeroDivisors
open KLinesIdealIndexPos
namespace GroundTheory.Heights₂.Heights
namespace LinesIdealIndexPos
theorem _root_.solution (h1 : LinesIsLattice.Statement) (h2 : LinesGenIndexTrans.Statement) :
    LinesIdealIndexPos.Statement := by
  intro K _ _ I hI
  have hL : ∀ J : FractionalIdeal (𝓞 K)⁰ K, J ≠ 0 →
      Submodule.IsLattice ℚ (((J : Submodule (𝓞 K) K).map (toOne K)).restrictScalars ℤ) :=
    fun J hJ => h1 K Unit _ (fg_and_span J hJ).1 (fg_and_span J hJ).2
  have hpos := (h2 (Unit → K) _ _ _ (hL I hI) (hL 1 one_ne_zero) (hL 1 one_ne_zero)).1
  have hmap : ∀ A B : AddSubgroup K, genIndex (A.map ((toOne K : K →+ (Unit → K))))
      (B.map (toOne K : K →+ (Unit → K))) = genIndex A B := by
    intro A B
    have hinj : Function.Injective (toOne K : K →+ (Unit → K)) := toOne_injective
    simp only [genIndex, AddSubgroup.relIndex_map_map_of_injective _ _ hinj]
  rw [FractionalIdeal.coe_one] at hpos
  unfold idealIndex
  rw [← hmap]
  exact hpos
end LinesIdealIndexPos
end GroundTheory.Heights₂.Heights
