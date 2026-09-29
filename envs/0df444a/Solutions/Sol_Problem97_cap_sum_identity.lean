-- Prove2me | solution 1 for Problem97.cap_sum_identity
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-08T06:05:52.5422+00:00
-- url     : https://prove2.me/submissions/df03f094-12dc-40d7-9381-056b7185ae98

/- Generated Prove2Me solution by exact Stage 2 source transformations.
   Target command: Erdos9796Proof.P97.Cap.Partition:2898:5138. -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_Cap_Partition
import Definitions.Def_Erdos9796Counting_Foundation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.SDiff

section Erdos9796CountingFragment_Erdos9796Proof_P97_Cap_Partition

open Problem97

/- Fragment from Erdos9796Proof.P97.Cap.Partition; source SHA-256 baaf503023695b8e0b1c19f8745478e6ec02a514e175bd113f5346c7d25a5e27 -/


/-!
# Cap-partition sum identity (Erdős Problem 97, Milestone 4)

Pure combinatorics extracted from the geometric setup in the universal
proof of Erdős Problem 97 (`p97-positive-defect-bridge`).

**Geometric origin.** In the universal-descent argument for Problem 97
(see `docs/97-uniform-theorem-closure-plan.md`), a convex counterexample
`P` to the 4-equidistant property carries three "caps" `C₁, C₂, C₃` cut
out by closed chains between three selected Moser vertices.  Each Moser vertex lies on exactly two opposite caps and
every other vertex on exactly one of the three chains, so

  `|C₁| + |C₂| + |C₃| = n + 3`

where `n = |P|`.

The geometry only enters via the membership pattern.  Once you fix it,
the identity is a pure counting lemma:

* a finset `S` (the vertex set),
* a 3-element subset `M ⊆ S` (the Moser vertices),
* three subsets `C₁, C₂, C₃ ⊆ S` such that every Moser vertex hits
  exactly two of them and every non-Moser vertex hits exactly one,

then `|C₁| + |C₂| + |C₃| = |S| + 3`.

Both pieces of data ("Moser vertex ⇒ in exactly two caps" and
"non-Moser ⇒ in exactly one cap") are packaged in a structure
`CapPartition` so the geometric obligation can hand the combinatorics
a single bundled object.

This is `p97-cap-sum-identity` (Milestone 4 sub-step 2 of 4).  It is
independent of the geometric existence proofs and provable from the
structural setup alone.
-/

open Finset






theorem solution {α : Type*} [DecidableEq α]
    {S M : Finset α} (cp : CapPartition S M) :
    cp.C1.card + cp.C2.card + cp.C3.card = S.card + 3 := by
  classical
  -- Express each cap's card as a sum of indicator-1's over `S`.
  -- Uses `C ⊆ S`: every element of `C` is counted, no element outside
  -- `C` contributes a 1.
  have hC : ∀ (C : Finset α), C ⊆ S →
      C.card = ∑ v ∈ S, (if v ∈ C then 1 else 0) := by
    intro C h
    rw [← card_filter (fun v => v ∈ C) S]
    congr 1
    ext x
    simp only [mem_filter]
    exact ⟨fun hx => ⟨h hx, hx⟩, fun ⟨_, hx⟩ => hx⟩
  -- Abbreviate the three-indicator sum per vertex.
  set f : α → ℕ := fun v =>
    (if v ∈ cp.C1 then 1 else 0)
      + (if v ∈ cp.C2 then 1 else 0)
      + (if v ∈ cp.C3 then 1 else 0) with hf
  -- Rewrite LHS as ∑_{v ∈ S} f v.
  rw [hC cp.C1 cp.C1_sub, hC cp.C2 cp.C2_sub, hC cp.C3 cp.C3_sub]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  change ∑ v ∈ S, f v = S.card + 3
  -- Split `S` into `M ∪ (S \ M)`.
  rw [← Finset.sum_sdiff cp.M_sub]
  -- Moser contribution: ∑_{v ∈ M} 2 = 2 · 3 = 6.
  have hM : ∑ v ∈ M, f v = 6 := by
    have h2 : ∀ v ∈ M, f v = 2 := cp.moser_in_two
    rw [Finset.sum_congr rfl h2, Finset.sum_const, cp.M_card]
    decide
  -- Non-Moser contribution: ∑_{v ∈ S \ M} 1 = |S| - 3.
  have hNonM : ∑ v ∈ S \ M, f v = S.card - 3 := by
    have h1 : ∀ v ∈ S \ M, f v = 1 := by
      intro v hv
      rcases Finset.mem_sdiff.mp hv with ⟨hvS, hvnM⟩
      exact cp.nonmoser_in_one v hvS hvnM
    rw [Finset.sum_congr rfl h1, Finset.sum_const]
    rw [Finset.card_sdiff_of_subset cp.M_sub, cp.M_card]
    simp
  rw [hM, hNonM]
  -- |S| ≥ 3 so ℕ subtraction is well-behaved.
  have hSge : 3 ≤ S.card := by
    rw [← cp.M_card]
    exact Finset.card_le_card cp.M_sub
  omega

end Erdos9796CountingFragment_Erdos9796Proof_P97_Cap_Partition
