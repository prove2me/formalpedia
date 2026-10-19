-- Prove2me | solution 1 for PermanentRollout.sourceTreeBlockMatrix_permanent_eq_separated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:10.343013+00:00
-- url     : https://prove2.me/submissions/4059654f-6f76-4ad2-b090-0c24ff74816b

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_sourceBlockMatrix_permanent_eq_matchingExpansion
import Theorems.Thm_PermanentRollout_sourceBlockAlpha_algebraMap
import Theorems.Thm_PermanentRollout_sourceTreeMatrix_alpha_eq_block_sum
import Theorems.Thm_PermanentRollout_sourceRowBlock_weighted_minor_sum

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution
    {R : Type*} [CommSemiring R] [Algebra ℂ R]
    (b t s d : ℕ) (hdpos : 0 < d) (hd : d ≤ t)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ d)
    (tree : BlockTree (Fin b))
    (hnodup : tree.leafList.Nodup)
    (hleaves : tree.leaves = Finset.univ)
    (X : Matrix (Fin (b * t)) (Fin s) R) :
    rectangularPermanent
        (sourceBlockMatrix (b * t) s d X
          (fun row column =>
            algebraMap ℂ R
              (sourceTreeMatrix b t d hd ζ tree hnodup hleaves row column))) =
      (((s - d).factorial : ℕ) : R) *
        algebraMap ℂ R (((t - d).factorial : ℕ) : ℂ) *
        algebraMap ℂ R ((((t.factorial : ℕ) : ℂ) ^ (b - 1))) *
        ∑ h : Fin b,
          algebraMap ℂ R
              (subtreeCoefficient
                (((-1 : ℂ) ^ (d + 1)) * (2 : ℂ) ^ d) tree h) *
            sourceRowBlockMinorSum b t s d X h := by
  classical
  have hb : 0 < b := by
    have hleaf : tree.leafList.length > 0 := tree_leafList_length_pos tree
    rw [sourceTree_leafList_length b tree hnodup hleaves] at hleaf
    exact hleaf
  have hrows : d ≤ b * t := by
    calc
      d ≤ t := hd
      _ ≤ b * t := Nat.le_mul_of_pos_left t hb
  rw [sourceBlockMatrix_permanent_eq_matchingExpansion
    (b * t) s d hrows X
    (fun row column =>
      algebraMap ℂ R
        (sourceTreeMatrix b t d hd ζ tree hnodup hleaves row column))]
  unfold sourceBlockMatchingExpansion
  let common : R :=
    algebraMap ℂ R (((t - d).factorial : ℕ) : ℂ) *
      algebraMap ℂ R ((((t.factorial : ℕ) : ℂ) ^ (b - 1)))
  let weight : Fin b → R := fun h =>
    algebraMap ℂ R
      (subtreeCoefficient
        (((-1 : ℂ) ^ (d + 1)) * (2 : ℂ) ^ d) tree h)
  have hcoefficient (omitted : Finset (Fin (b * t)))
      (homitted : omitted.card = d) :
      sourceBlockAlpha (b * t) d
          (fun row column =>
            algebraMap ℂ R
              (sourceTreeMatrix b t d hd ζ tree hnodup hleaves
                row column)) omitted =
        common * ∑ h : Fin b,
          if omitted ⊆ sourceRowBlock b t h then weight h else 0 := by
    rw [sourceBlockAlpha_algebraMap,
      sourceTreeMatrix_alpha_eq_block_sum
        b t d hdpos hd hζ tree hnodup hleaves omitted homitted]
    simp only [map_mul, map_sum]
    change common *
      (∑ h : Fin b,
        algebraMap ℂ R
          (if omitted ⊆ sourceRowBlock b t h then
            subtreeCoefficient
              (((-1 : ℂ) ^ (d + 1)) * (2 : ℂ) ^ d) tree h
          else 0)) =
      common *
        ∑ h : Fin b,
          if omitted ⊆ sourceRowBlock b t h then weight h else 0
    congr 1
    apply Finset.sum_congr rfl
    intro h _
    split <;> simp [weight]
  have hsum :
      (∑ omitted ∈ (Finset.univ : Finset (Fin (b * t))).powersetCard d,
        ∑ columns ∈ (Finset.univ : Finset (Fin s)).powersetCard d,
          sourceBlockAlpha (b * t) d
              (fun row column =>
                algebraMap ℂ R
                  (sourceTreeMatrix b t d hd ζ tree hnodup hleaves
                    row column)) omitted *
            sourceBlockMinor (b * t) s X omitted columns) =
        common *
          ∑ h : Fin b, weight h * sourceRowBlockMinorSum b t s d X h := by
    calc
      _ = common *
          (∑ omitted ∈
            (Finset.univ : Finset (Fin (b * t))).powersetCard d,
            (∑ h : Fin b,
              if omitted ⊆ sourceRowBlock b t h then weight h else 0) *
              ∑ columns ∈ (Finset.univ : Finset (Fin s)).powersetCard d,
                sourceBlockMinor (b * t) s X omitted columns) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro omitted homitted
            rw [hcoefficient omitted
              (Finset.mem_powersetCard.mp homitted).2]
            simp only [← Finset.mul_sum, mul_assoc]
      _ = _ := by
        rw [sourceRowBlock_weighted_minor_sum b t s d X weight]
  rw [hsum]
  dsimp [common, weight]
  ring
end PermanentRollout
