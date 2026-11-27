-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_LocCyclePos_proof_e557bf920e36
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:13:00.188349+00:00
-- url     : https://prove2.me/submissions/9910f17e-a2c8-47f9-b8a4-6ce42b31d58c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsLocalCoeffLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PLocCyclePos
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_localizedModule_quot_nontrivial_8da5c23aeba2
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_locLen_ne_top


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace LocCyclePos
theorem _root_.solution : LocCyclePos.Statement := by
  intro R _ _ J W hW
  have : W.IsPrime := hW.1.1
  have hfin := ReciprocityTheory.ChartRestriction.G.AI.I1.locLen_ne_top hW
  unfold ReciprocityTheory.ChartRestriction.G.AI.locLen at hfin
  have := localizedModule_quot_nontrivial J W hW.1.2
  have hpos : 0 < Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (R ⧸ J)) :=
    Module.length_pos
  unfold locCycle
  rw [dif_pos hW]
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
  simp only at hn
  rw [← hn] at hpos ⊢
  simp only [ENat.toNat_natCast, Nat.cast_pos]
  exact_mod_cast hpos
end LocCyclePos
end GroundTheory.Heights₂.Heights.NumbersDVR
