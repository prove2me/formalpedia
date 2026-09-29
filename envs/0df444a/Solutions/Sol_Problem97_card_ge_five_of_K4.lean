-- Prove2me | solution 1 for Problem97.card_ge_five_of_K4
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-08T06:06:13.655137+00:00
-- url     : https://prove2.me/submissions/6d912ef5-ac2d-4cb7-be85-d219cda69c52

/- Generated Prove2Me solution by exact Stage 2 source transformations.
   Target command: Erdos9796Proof.P97.Counting:761:1564. -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_Foundation

section Erdos9796CountingFragment_Erdos9796Proof_P97_Counting

open Problem97

/- Fragment from Erdos9796Proof.P97.Counting; source SHA-256 1bc8e15663c147d582d82d71a22bf654f8becdb1003f0aef828d47271d204523 -/


/-!
# Counting obstruction: `9 ≤ |A|` (Milestone 3)

This module packages the proven lower bound
`Problem97.six_mul_card_le_iCount_of_K4` and the proven arithmetic core
`Problem97.counting_arithmetic` into the intermediate theorem
`Problem97.counterexample_card_ge_nine_of_iCount_upper_bound`.

The top-level theorem `Problem97.counterexample_card_ge_nine` now
instantiates that reducer with the circumscribed-branch CGN closure
`Problem97.CGN8_circumscribed_iCount_upper_bound`.
-/

open scoped EuclideanGeometry
open Finset




theorem solution {A : Finset ℝ²} (hne : A.Nonempty)
    (hK4 : HasNEquidistantProperty 4 A) : 5 ≤ A.card := by
  classical
  obtain ⟨p, hp⟩ := hne
  obtain ⟨r, hrpos, hcount⟩ := hK4 p hp
  set S : Finset ℝ² := A.filter (fun q => dist p q = r) with hS
  have hScard : 4 ≤ S.card := hcount
  have hSsub : S ⊆ A.erase p := by
    intro q hqS
    rcases mem_filter.mp hqS with ⟨hqA, hqr⟩
    refine mem_erase.mpr ⟨?_, hqA⟩
    intro hqp
    rw [hqp, dist_self] at hqr
    linarith
  have h4erase : 4 ≤ (A.erase p).card := hScard.trans (card_le_card hSsub)
  have herase : (A.erase p).card = A.card - 1 := card_erase_of_mem hp
  omega

end Erdos9796CountingFragment_Erdos9796Proof_P97_Counting
