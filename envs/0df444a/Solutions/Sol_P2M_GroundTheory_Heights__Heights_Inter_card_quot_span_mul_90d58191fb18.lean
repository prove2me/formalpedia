-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_card_quot_span_mul_90d58191fb18
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:25:42.591807+00:00
-- url     : https://prove2.me/submissions/8a95f491-65f9-4ad2-84cb-eace3f240538

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_XcNotMemOfIsRelevant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerFurther
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_TwoMemFunFieldSpecZ
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerTer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerMore
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LogCardLocIdealUnitMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution {S : Type*} [CommRing S] [IsDomain S] (u v : S) (hu : u ≠ 0) :
    Nat.card (S ⧸ Ideal.span {u * v}) = Nat.card (S ⧸ Ideal.span {u}) * Nat.card (S ⧸ Ideal.span {v}) := by
  let f : S →+ S := AddMonoidHom.mulLeft u
  have hf : Function.Injective f := fun a b h => mul_left_cancel₀ hu h
  have e1 : (Ideal.span {v}).toAddSubgroup.map f = (Ideal.span {u * v}).toAddSubgroup := by
    ext z
    simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨_, ⟨r, rfl⟩, rfl⟩
      exact ⟨r, by simp only [f, AddMonoidHom.coe_mulLeft]; ring⟩
    · rintro ⟨r, rfl⟩
      exact ⟨r * v, ⟨r, rfl⟩, by simp only [f, AddMonoidHom.coe_mulLeft]; ring⟩
  have e2 : (⊤ : AddSubgroup S).map f = (Ideal.span {u}).toAddSubgroup := by
    ext z
    simp only [AddSubgroup.mem_map, AddSubgroup.mem_top, true_and, Submodule.mem_toAddSubgroup,
      Ideal.mem_span_singleton', f, AddMonoidHom.coe_mulLeft]
    exact ⟨fun ⟨y, hy⟩ => ⟨y, by rw [← hy, mul_comm]⟩, fun ⟨r, hr⟩ => ⟨r, by rw [← hr, mul_comm]⟩⟩
  have hle : (Ideal.span {u * v}).toAddSubgroup ≤ (Ideal.span {u}).toAddSubgroup :=
    fun z hz => Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_right u v) hz
  have h2 : (Ideal.span {u * v}).toAddSubgroup.relIndex (Ideal.span {u}).toAddSubgroup =
      (Ideal.span {v}).toAddSubgroup.index := by
    rw [← e1, ← e2, AddSubgroup.relIndex_map_map_of_injective _ _ hf, AddSubgroup.relIndex_top_right]
  have hc : ∀ I : Ideal S, Nat.card (S ⧸ I) = I.toAddSubgroup.index :=
    fun I => (AddSubgroup.index_eq_card _).symm
  rw [hc, hc, hc, ← AddSubgroup.relIndex_mul_index hle, h2, mul_comm]
end GroundTheory.Heights₂.Heights.Inter
