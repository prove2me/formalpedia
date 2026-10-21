-- Prove2me | solution 1 for RawBlending.UB.theorem_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T14:59:41.83516+00:00
-- url     : https://prove2.me/submissions/0a614830-03fb-4c4d-b58a-c89d95164a6e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RawBlending_UB_Policy
import Theorems.Thm_RawBlending_UB_induction_H
import Theorems.Thm_RawBlending_UB_lemma_3_a
import Theorems.Thm_RawBlending_UB_theorem_1_production

open RawBlending.UB in
theorem solution (d : Data) (hd : d.Standing) (t : ℕ)
    (ht : 1 ≤ t) (htT : t ≤ d.T) :
    ∃ C : Curves, IsUBCurves (J d t) d.a1 d.a2 C ∧
      ∀ D R : ℝ, 0 ≤ D → 0 ≤ R →
        RegionsCover C d.a1 d.a2 D R ∧
        (d.a1 * R < D → RegionsDisjoint C d.a1 d.a2 D R) ∧
        ∀ y : Vec, y ∈ orthant →
          Minimizes (J d t) (E2 d.a1 d.a2 y D R)
            (ubAction C d.a1 d.a2 D R y) := by
  have hH : H d t := induction_H d hd t ht htT
  have hJ : IsJClass (J d t) := lemma_3_a d hd t ht htT hH
  exact theorem_1_production (J d t) hJ d.a1 d.a2 hd.2.1 hd.2.2.1
