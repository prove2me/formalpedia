-- Prove2me | solution 1 for ThreeSum.LocalCoverBounds.pow_le_choose_mul_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:13:10.255412+00:00
-- url     : https://prove2.me/submissions/c2a6d351-b85c-4531-a780-05036b399cda

import Definitions.Def_Submission_ThreeSum_LayerCounts
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Sqrt
import Mathlib.NumberTheory.Bertrand
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices



set_option autoImplicit false
open ThreeSum ThreeSum.LocalCoverBounds
open scoped BigOperators
namespace ThreeSum.LocalCoverBounds
theorem _root_.solution (c r : ℕ) : c ^ r ≤ (c * r).choose r := by
  let graph (f : Fin r → Fin c) : Finset (Fin r × Fin c) :=
    Finset.univ.image (fun i => (i, f i))
  have hgcard (f : Fin r → Fin c) : (graph f).card = r := by
    change (Finset.univ.image (fun i : Fin r => (i, f i))).card = r
    rw [Finset.card_image_of_injective]
    · simp
    · intro i j he
      exact congrArg Prod.fst he
  have hginj : Function.Injective graph := by
    intro f g he
    funext i
    have hm : (i, f i) ∈ graph g := by
      rw [← he]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hm
    have hji : j = i := congrArg Prod.fst hj
    subst j
    exact (congrArg Prod.snd hj).symm
  have hcount : (Finset.univ : Finset (Fin r → Fin c)).card ≤
      ((Finset.univ : Finset (Fin r × Fin c)).powersetCard r).card := by
    apply Finset.card_le_card_of_injOn graph
    · intro f _
      exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hgcard f⟩
    · intro f _ g _ he
      exact hginj he
  simpa [Finset.card_powersetCard, Nat.mul_comm] using hcount
end ThreeSum.LocalCoverBounds
