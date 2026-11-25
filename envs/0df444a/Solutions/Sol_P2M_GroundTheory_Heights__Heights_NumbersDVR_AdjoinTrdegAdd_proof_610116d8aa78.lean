-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_AdjoinTrdegAdd_proof_610116d8aa78
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:22:47.745231+00:00
-- url     : https://prove2.me/submissions/a8b4bc98-8d20-49e7-aa1c-25228099444b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsAdjoinTrdegAdd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PAdjoinTrdegAdd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_AdjoinTrdegAdd_trdeg_adjoin_eq_of_family_7abcbe3c35c9

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
open Algebra Cardinal Set
noncomputable section
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace AdjoinTrdegAdd
theorem _root_.solution : AdjoinTrdegAdd.Statement := by
  intro R _ L _ _ _ hinj s t ι _ x hxt hx hxalg
  have : FaithfulSMul R L := (faithfulSMul_iff_algebraMap_injective R L).mpr hinj
  obtain ⟨b, hb⟩ := (AlgebraicIndependent.matroid R L).exists_isBasis s (by simp)
  obtain ⟨hbi, hbs, hbalg⟩ := AlgebraicIndependent.matroid_isBasis_iff.mp hb
  have hbi' : AlgebraicIndependent R ((↑) : b → L) := hbi

  have h1 : trdeg R (adjoin R s) = #b :=
    AdjoinTrdegAdd.trdeg_adjoin_eq_of_family s ((↑) : b → L) (by rw [Subtype.range_coe]; exact hbs) hbi'
      (by rw [Subtype.range_coe]; exact hbalg)

  let _ : Algebra (adjoin R b) (adjoin R s) := (Subalgebra.inclusion (adjoin_mono hbs)).toAlgebra
  have : IsScalarTower (adjoin R b) (adjoin R s) L := .of_algebraMap_eq fun _ => rfl
  have hxb : AlgebraicIndependent (adjoin R (range ((↑) : b → L))) x := by
    rw [Subtype.range_coe]
    exact hx.restrictScalars (Subalgebra.inclusion_injective _)
  have hsum : AlgebraicIndependent R (Sum.elim x ((↑) : b → L)) :=
    AlgebraicIndependent.sumElim_iff.mpr ⟨hbi', hxb⟩
  have hrange : range (Sum.elim x ((↑) : b → L)) = range x ∪ b := by
    rw [Set.Sum.elim_range, Subtype.range_coe]

  have hs : ∀ a ∈ s, IsAlgebraic (adjoin R (range x ∪ b)) a := fun a ha =>
    (hbalg a ha).adjoin_of_forall_isAlgebraic fun y hy => (hy.2 (Or.inr hy.1)).elim
  have hst : ∀ a ∈ s ∪ t, IsAlgebraic (adjoin R (range (Sum.elim x ((↑) : b → L)))) a := by
    rw [hrange]
    rintro a (ha | ha)
    · exact hs a ha
    · refine (hxalg a ha).adjoin_of_forall_isAlgebraic fun y hy => ?_
      rcases hy.1 with hy1 | hy1
      · exact hs y hy1
      · exact (hy.2 (Or.inl hy1)).elim
  have h2 : trdeg R (adjoin R (s ∪ t)) = #(ι ⊕ b) :=
    AdjoinTrdegAdd.trdeg_adjoin_eq_of_family (s ∪ t) (Sum.elim x ((↑) : b → L))
      (by rw [hrange]; exact union_subset (hxt.trans subset_union_right) (hbs.trans subset_union_left))
      hsum hst
  rw [h2, h1, mk_sum, lift_id, lift_id, mk_fintype, add_comm]
end AdjoinTrdegAdd
end GroundTheory.Heights₂.Heights.NumbersDVR
