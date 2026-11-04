-- Prove2me | solution 1 for ThreeSum.TernaryCoverHighMoment.raw_high_moment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:04:33.357385+00:00
-- url     : https://prove2.me/submissions/39fee17a-439e-4c85-9f99-ce8158ed4dee

import Definitions.Def_Submission_ThreeSum_TernaryCoverTupleCount
import Definitions.Def_Submission_ThreeSum_TernaryCoverUniformRank
import Definitions.Def_Submission_ThreeSum_TernaryCoverMoments
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_Submission_ThreeSum_TernaryCoverHighMoment
import Theorems.Thm_ThreeSum_TernaryCoverHighMoment_jointEvent_rows
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_TernaryCoverMoments_moment_bound_of_classes
import Theorems.Thm_ThreeSum_TernaryCoverRelations_possibleSpans_card
import Theorems.Thm_ThreeSum_TernaryCoverTupleCount_tupleSet_card_le
import Theorems.Thm_ThreeSum_TernaryCoverUniformRank_prescribedEvent_rank_bound
attribute [local simp] ThreeSum.HashFamily.hashMap_apply



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverHighMoment
open Finset TernaryCoverRankFibers TernaryCoverTupleCount
open TernaryCoverRelations TernaryCoverUniformRank TernaryCoverMoments
open scoped BigOperators
variable {K E σ : Type*} [Field K] [Fintype E] [Fintype σ] [DecidableEq σ]
variable [Fintype K] [DecidableEq K]
namespace ThreeSum.TernaryCoverHighMoment
theorem _root_.solution (left right : E → σ → Fin 3)
    (hinj : Function.Injective (fun e => (castWord (K := K) (left e), castWord (K := K) (right e))))
    (hE : Fintype.card E ≤ Fintype.card K ^ 2)
    (hprojection : ∀ β γ : K, (β ≠ 0 ∨ γ ≠ 0) → ∀ q : σ → K,
      (projectionFiber (fun e => castWord (K := K) (left e))
        (fun e => castWord (K := K) (right e)) β γ q).card ≤ Fintype.card K)
    (k : ℕ) (a b : K) :
    (∑ w, HashFamily.incidenceCount (rawEvents left right a b) w ^ k) ≤
      3 ^ (4*k^2) * Fintype.card (σ → K) := by
  classical
  let C := possibleSpans K (k*2)
  let rank : C → ℕ := fun c => Module.finrank K c.val
  have hcount (c : C) :
      (univ.filter fun es : Fin k → E => classify left right es = c).card ≤ Fintype.card K ^ rank c := by
    let S := c.val.comap (flattenPairs (K := K) k).toLinearMap
    have hsub : (univ.filter fun es : Fin k → E => classify left right es = c) ⊆
        tupleSet (fun e => castWord (K := K) (left e)) (fun e => castWord (K := K) (right e)) k S := by
      intro es hes
      have hc := congrArg Subtype.val (mem_filter.mp hes).2
      apply mem_filter.mpr
      refine ⟨mem_univ _, ?_⟩
      intro i
      change flattenPairs k (tupleColumn (fun e => castWord (K := K) (left e))
        (fun e => castWord (K := K) (right e)) es i) ∈ c.val
      rw [← hc]
      exact Submodule.subset_span (Set.mem_range_self i)
    have hr : Module.finrank K c.val = Module.finrank K S := by
      have h := LinearEquiv.finrank_eq ((flattenPairs (K := K) k).symm.submoduleMap c.val)
      have heq : c.val.map (flattenPairs (K := K) k).symm.toLinearMap = S :=
        c.val.map_equiv_eq_comap_symm (flattenPairs (K := K) k).symm
      rwa [heq] at h
    exact (card_le_card hsub).trans (by
      simpa [rank, ← hr] using tupleSet_card_le
        (fun e => castWord (K := K) (left e)) (fun e => castWord (K := K) (right e))
        (Fintype.card K) hinj hE hprojection k S)
  have hhash (es : Fin k → E) :
      Fintype.card K ^ rank (classify left right es) * (jointEvent (rawEvents left right a b) es).card ≤
        Fintype.card (σ → K) := by
    rw [jointEvent_rows]
    exact prescribedEvent_rank_bound (rows left right es) _
  have h := moment_bound_of_classes (rawEvents left right a b) k (Fintype.card K)
    Fintype.card_pos (classify left right) rank hcount hhash
  have hC : Fintype.card C ≤ 3 ^ (4*k^2) := by
    dsimp [C]
    rw [Fintype.card_coe]
    convert possibleSpans_card (K := K) (k*2) using 1 <;> congr 1 <;> ring
  exact h.trans (Nat.mul_le_mul_right _ hC)
end ThreeSum.TernaryCoverHighMoment
