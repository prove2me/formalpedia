-- Prove2me | solution 1 for ThreeSum.TernaryCoverUniformRank.prescribedEvent_rank_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:07:08.748856+00:00
-- url     : https://prove2.me/submissions/2d5f1060-7636-4873-bbbd-10596e4b630d

import Definitions.Def_Submission_ThreeSum_HashFamily
import Definitions.Def_Submission_ThreeSum_TernaryCoverRelations
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Definitions.Def_Submission_ThreeSum_TernaryCoverUniformRank
import Theorems.Thm_ThreeSum_TernaryCoverUniformRank_row_rank_eq_column_rank
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_HashFamily_hash_fiber_card
attribute [local simp] ThreeSum.HashFamily.hashMap_apply



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverUniformRank
open Finset TernaryCoverRelations
open scoped BigOperators
variable {K σ : Type*} [Field K] [Fintype σ] [DecidableEq σ]
variable [Fintype K] [DecidableEq K]
namespace ThreeSum.TernaryCoverUniformRank
theorem _root_.solution {d : ℕ} (v : Fin d → σ → K) (target : Fin d → K) :
    Fintype.card K ^ Module.finrank K (columnSpan v) * (prescribedEvent v target).card ≤
      Fintype.card (σ → K) := by
  classical
  let S := Submodule.span K (Set.range v)
  let r := Module.finrank K S
  obtain ⟨f, hf, _, hind⟩ := Submodule.exists_fun_fin_finrank_span_eq K (Set.range v)
  let pick : Fin r → Fin d := fun i => Classical.choose (hf i)
  have hpick (i : Fin r) : v (pick i) = f i := Classical.choose_spec (hf i)
  let target' : Fin r → K := fun i => target (pick i)
  let basisEvent : Finset (σ → K) := univ.filter fun w => HashFamily.hashMap f w = target'
  have hsub : prescribedEvent v target ⊆ basisEvent := by
    intro w hw
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    funext i
    have hi := (mem_filter.mp hw).2 (pick i)
    change (∑ j, f i j * w j) = target (pick i)
    rw [← hpick]
    exact hi
  have hb : Fintype.card K ^ r * basisEvent.card = Fintype.card (σ → K) := by
    simpa [basisEvent, r, S] using HashFamily.hash_fiber_card hind target'
  have hr : r = Module.finrank K (columnSpan v) := row_rank_eq_column_rank v
  rw [← hr]
  exact (Nat.mul_le_mul_left _ (card_le_card hsub)).trans_eq hb
end ThreeSum.TernaryCoverUniformRank
