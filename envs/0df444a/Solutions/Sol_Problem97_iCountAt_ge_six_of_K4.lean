-- Prove2me | solution 1 for Problem97.iCountAt_ge_six_of_K4
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-08T06:06:21.461228+00:00
-- url     : https://prove2.me/submissions/3e14fba6-d123-4c3a-ad66-fee60ed5655d

/- Generated Prove2Me solution by exact Stage 2 source transformations.
   Target command: Erdos9796Proof.P97.IsoscelesCount:5426:6846. -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_Foundation
import Definitions.Def_Erdos9796Counting_IsoscelesCount
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Powerset

section Erdos9796CountingFragment_Erdos9796Proof_P97_IsoscelesCount

open Problem97

/- Fragment from Erdos9796Proof.P97.IsoscelesCount; source SHA-256 207564b11a38e9270192c8e5de3202b113b7f89c7ece5af3bc12954928d3013c -/


/-!
# Isosceles count for Erdős Problem 97 (Dumitrescu lower bound, Milestone 3)

Defines the per-vertex and total isosceles count of a finite point set,
in the Dumitrescu 2006 / Nivasch–Pach–Pinchasi–Zerbib 2013 convention
(equilaterals counted three times), and proves the easy lower bound:

  Per-vertex `K4` ⇒ each vertex contributes `≥ C(4,2) = 6` isosceles pairs.
  Summing: `6 · |A| ≤ I(A)`.

The matching upper bound `I(A) ≤ (11·|A|²−18·|A|)/12` for convex point
sets is Dumitrescu 2006 eq. (5), still open
(`p97-isosceles-count-upper-bound`).

References: doc slug `p97-isosceles-obstruction`.
-/

set_option linter.style.openClassical false

open scoped EuclideanGeometry
open Finset Classical


















theorem solution (A : Finset ℝ²) (p : ℝ²)
    (hp : HasNEquidistantPointsAt 4 A p) : 6 ≤ iCountAt A p := by
  obtain ⟨r, hrpos, hcount⟩ := hp
  -- Let `S` be the 4-equidistant class at `p`.
  set S : Finset ℝ² := A.filter (fun q => dist p q = r) with hS
  have hScard : 4 ≤ S.card := hcount
  -- `S ⊆ A.erase p`: every element of `S` is in `A` at positive distance from `p`.
  have hSsub : S ⊆ A.erase p := by
    intro q hqS
    rcases mem_filter.mp hqS with ⟨hqA, hqr⟩
    refine mem_erase.mpr ⟨?_, hqA⟩
    intro hqp; rw [hqp] at hqr; rw [dist_self] at hqr; linarith
  -- Every 2-element subset of `S` is in `IsoscelesPairsAt A p`.
  have hsubInIso : S.powersetCard 2 ⊆ IsoscelesPairsAt A p := by
    intro t ht
    rcases mem_powersetCard.mp ht with ⟨htsub, htcard⟩
    refine mem_filter.mpr ⟨?_, ⟨r, ?_⟩⟩
    · exact mem_powersetCard.mpr ⟨htsub.trans hSsub, htcard⟩
    · intro q hqt
      exact (mem_filter.mp (htsub hqt)).2
  -- Cardinality bookkeeping: `C(S.card, 2) ≥ C(4, 2) = 6`.
  calc 6 = (4 : ℕ).choose 2 := by decide
    _ ≤ S.card.choose 2 := Nat.choose_le_choose 2 hScard
    _ = (S.powersetCard 2).card := (S.card_powersetCard 2).symm
    _ ≤ iCountAt A p := card_le_card hsubInIso

end Erdos9796CountingFragment_Erdos9796Proof_P97_IsoscelesCount
