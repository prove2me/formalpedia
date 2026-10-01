-- Prove2me | solution 1 for burau_faithful_three_reduction
-- status  : ACCEPTED   (prove)
-- author  : @lt9
-- created : 2026-09-30T21:20:48.877706+00:00
-- url     : https://prove2.me/submissions/6196d978-97e5-48cf-b2c8-f6f8217aaef5

import Definitions.Def_BurauFaithful_UnreducedBurau
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup

set_option autoImplicit false

/-- Reduction: a free-group criterion for `BurauFaithful.burauRep 3` (with respect to **Artin's**
relations, so that the statement is self-contained) implies faithfulness of the unreduced Burau
representation of `B₃`. -/
theorem solution
    (hc : ∀ w : FreeGroup (Fin 2),
      BurauFaithful.burauRep 3 (PresentedGroup.mk (BraidsLinksMCG.braidRels 3) w) = 1 ↔
        w ∈ Subgroup.normalClosure (BraidsLinksMCG.braidRels 3)) :
    Function.Injective (BurauFaithful.burauRep 3) := by
  rw [injective_iff_map_eq_one]
  intro β hβ
  obtain ⟨w, rfl⟩ := PresentedGroup.mk_surjective (BraidsLinksMCG.braidRels 3) β
  exact PresentedGroup.mk_eq_one_iff.mpr ((hc w).mp hβ)
