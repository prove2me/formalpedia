-- Prove2me | solution 1 for ThreeSum.TernaryCoverRankFibers.affineFiber_card_le_of_proper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:08:33.107821+00:00
-- url     : https://prove2.me/submissions/21ead86d-ae38-4d28-b4ae-80e73cb6949e

import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryCoverRankFibers
import Theorems.Thm_ThreeSum_TernaryCoverRankFibers_exists_annihilating_projection

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverRankFibers
open Finset
variable {K : Type*} [Field K]
variable {E ι : Type*} [Fintype E] [Fintype ι] [DecidableEq K]
namespace ThreeSum.TernaryCoverRankFibers
theorem _root_.solution (left right : E → ι → K) (P : ℕ)
    (hprojection : ∀ β γ : K, (β ≠ 0 ∨ γ ≠ 0) → ∀ q : ι → K,
      (projectionFiber left right β γ q).card ≤ P)
    (V : Submodule K (K × K)) (hV : V ≠ ⊤) (offset : ι → K × K) :
    (affineFiber left right V offset).card ≤ P := by
  classical
  obtain ⟨β, γ, hnonzero, hann⟩ := exists_annihilating_projection V hV
  let q : ι → K := fun i => β * (offset i).1 + γ * (offset i).2
  have hsub : affineFiber left right V offset ⊆ projectionFiber left right β γ q := by
    intro e he
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    intro i
    have h := hann ((left e i, right e i) - offset i) ((mem_filter.mp he).2 i)
    change β * (left e i - (offset i).1) + γ * (right e i - (offset i).2) = 0 at h
    dsimp [q]
    linear_combination h
  exact (card_le_card hsub).trans (hprojection β γ hnonzero q)
end ThreeSum.TernaryCoverRankFibers
