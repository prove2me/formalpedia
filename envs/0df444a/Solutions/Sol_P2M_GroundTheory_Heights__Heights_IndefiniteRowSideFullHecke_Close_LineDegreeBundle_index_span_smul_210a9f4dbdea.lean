-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_LineDegreeBundle_index_span_smul_210a9f4dbdea
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:56:09.220381+00:00
-- url     : https://prove2.me/submissions/38252b5b-7398-4cfd-9faa-23f9b72784bd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_LineDegreeBundleStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PointHeightDegreeHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PLineDegreeBundle

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
open NumberField Matrix TensorProduct ComplexAt
open scoped ComplexOrder nonZeroDivisors
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
namespace LineDegreeBundle
theorem _root_.solution {R N : Type*} [CommRing R] [AddCommGroup N] [Module R N]
    [IsDomain R] [Module.IsTorsionFree R N] {x : N} (hx : x ≠ 0) (a : R) :
    (Submodule.span R {a • x}).toAddSubgroup.index =
      Submodule.cardQuot (Ideal.span {a} : Ideal R) * (Submodule.span R {x}).toAddSubgroup.index := by
  have hle : (Submodule.span R {a • x}).toAddSubgroup ≤ (Submodule.span R {x}).toAddSubgroup :=
    Submodule.span_le.mpr (Set.singleton_subset_iff.mpr
      (Submodule.smul_mem _ a (Submodule.mem_span_singleton_self x)))
  rw [← AddSubgroup.relIndex_mul_index hle]
  congr 1
  have hg : Function.Injective (LinearMap.toSpanSingleton R N x) :=
    fun r s h ↦ smul_left_injective R hx h
  have h1 : Submodule.span R {a • x} = Submodule.map (LinearMap.toSpanSingleton R N x) (Ideal.span {a} : Submodule R R) := by
    rw [Submodule.map_span, Set.image_singleton, LinearMap.toSpanSingleton_apply]
  have h2 : Submodule.span R {x} = Submodule.map (LinearMap.toSpanSingleton R N x) (⊤ : Submodule R R) := by
    rw [Submodule.map_top, LinearMap.span_singleton_eq_range]
  rw [h1, h2, Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup,
    AddSubgroup.relIndex_map_map_of_injective _ _ hg, Submodule.top_toAddSubgroup,
    AddSubgroup.relIndex_top_right]
  rfl
end LineDegreeBundle
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
