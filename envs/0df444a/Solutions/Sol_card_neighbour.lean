-- Prove2me | solution 1 for card_neighbour
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:43:03.433689+00:00
-- url     : https://prove2.me/submissions/eaca7bc6-0f55-4414-8693-35ab42e68cbe

import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.NNRat.Floor
import Mathlib.Tactic.Rify
import Definitions.Def_Polychromatic_Colouring
import Definitions.Def_Polychromatic_Compactness
import Definitions.Def_Polychromatic_LocalLemma
import Definitions.Def_Polychromatic_Existence
import Theorems.Thm_card_sub_erase_zero_le
import Theorems.Thm_hasPolychromColouring_neg
import Theorems.Thm_hasPolychromColouring_univ
attribute [local simp] hasPolychromColouring_neg
attribute [local simp] hasPolychromColouring_univ



set_option autoImplicit true
open Finset
open Pointwise
variable {G : Type*} [AddCommGroup G]
open MeasureTheory ProbabilityTheory
theorem _root_.solution [DecidableEq G] {m : ℕ} {S X : Finset G} (hm : #S = m) {x : X} :
    #(X.attach.filter (fun i ↦ x.1 - i.1 ∈ (S - S).erase 0)) ≤ m * (m - 1) := by
  calc
    #({i ∈ X.attach | x.1 - i.1 ∈ (S - S).erase 0}) = #({i ∈ X | ↑x - i ∈ (S - S).erase 0}) := by
      rw [filter_attach (fun i ↦ x.1 - i ∈ (S - S).erase 0), card_map, card_attach]
    _ ≤ #(((S - S).erase 0).image (x.1 - ·)) := by
      apply card_le_card
      intro j
      simp only [mem_filter, mem_image, and_imp]
      intro i hi
      exact ⟨_, hi, by grind⟩
    _ ≤ #((S - S).erase 0) := card_image_le
    _ ≤ #S * (#S - 1) := card_sub_erase_zero_le
    _ = m * (m - 1) := by simp [hm]
