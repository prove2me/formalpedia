-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_lineBranch_branchesAt_31c740b2197d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:29:35.311377+00:00
-- url     : https://prove2.me/submissions/2acf7e78-b4dc-4a05-abd8-dbc82ab1a602

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivPushA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsDivPushMultComplex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsConeBranchLength
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_lineFun_cover_aae3546fad86

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial Filter Topology ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.Inter
namespace GroundTheory.Heights₂.Heights.Targets
theorem _root_.solution :
    ConeBranchesAt (⊥ : Ideal (MRing (PBlk 2))) (Xc 2 0) (Ideal.span {X ⟨(), 0⟩}) (d := 1) ptZeroOne
      (fun _ : Fin 1 => lineBranch) (fun _ => 1) := by
  refine ⟨fun _ => ⟨1, by simp [ptZeroOne]⟩, ?_,
    ⟨Metric.ball ptZeroOne (1 / 2), Metric.ball_mem_nhds _ (by norm_num), ?_⟩,
    fun j j' h => absurd (Subsingleton.elim j j') h,
    ⟨Metric.ball ptZeroOne (1 / 2), Metric.ball_mem_nhds _ (by norm_num), ?_⟩,
    fun _ => ⟨fun _ => 1, differentiableOn_const _, fun _ _ => one_ne_zero, fun t _ => ?_⟩⟩
  · intro f hf
    obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton.mp hf
    simp [ptZeroOne]
  · rintro v ⟨-, hv⟩
    obtain ⟨t, ht, htv, -⟩ := lineFun_cover v hv
    exact Set.mem_iUnion.mpr ⟨0, t, ht, htv⟩
  · rintro _ v ⟨hv0, hv⟩
    obtain ⟨t, ht, htv, ht0⟩ := lineFun_cover v hv
    have h0 : v ⟨(), 0⟩ = 0 := by
      simpa using hv0 _ (Ideal.subset_span (Set.mem_singleton _))
    exact ⟨t, ⟨ht, by simp [ht0, h0]⟩, htv⟩
  · simp [lineBranch, lineFun, Xc]
end GroundTheory.Heights₂.Heights.Targets
