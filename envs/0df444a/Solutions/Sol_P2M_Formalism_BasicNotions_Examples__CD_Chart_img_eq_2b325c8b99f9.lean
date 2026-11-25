-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__CD_Chart_img_eq_2b325c8b99f9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:30:50.126386+00:00
-- url     : https://prove2.me/submissions/36dc4ce5-a47f-4956-bbba-fad11bf3bfe9

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_LeOfEventuallyDown
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_HasStrictFDerivAtExpZero
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_ExistsDensity
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_Chart_mat_expG_1363518d9b59

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.CD
open MeasureTheory Filter Topology Metric NormedSpace Set
open scoped ENNReal NNReal
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
open Formalism.BasicNotions.Examples₂.CD.Chart
variable {V : Submodule ℝ 𝔸} {G : Type*} [Group G] [TopologicalSpace G] (C : Chart V G)
namespace Formalism.BasicNotions.Examples₂.CD.Chart
theorem _root_.solution (s : Set V) : C.img s = C.expG '' s := by
  ext g
  constructor
  · rintro ⟨X, hX, hg⟩
    refine ⟨X, hX, C.emb.injective ?_⟩
    rw [C.mat_expG, hg]
  · rintro ⟨X, hX, rfl⟩
    exact ⟨X, hX, C.mat_expG X⟩
end Formalism.BasicNotions.Examples₂.CD.Chart
