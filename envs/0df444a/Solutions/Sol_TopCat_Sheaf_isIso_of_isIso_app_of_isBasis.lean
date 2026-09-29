-- Prove2me | solution 1 for TopCat.Sheaf.isIso_of_isIso_app_of_isBasis
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/9180ce20-1069-5195-830a-547f76c470c2

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TopCat_Sheaf_isIso_of_isIso_app_of_isBasis

universe u v w u'

open CategoryTheory Opposite TopologicalSpace

theorem solution {C : Type u} [Category.{v} C] {X : TopCat.{w}}
    {ι : Type u'} {B : ι → Opens X} (hB : Opens.IsBasis (Set.range B)) {F G : TopCat.Sheaf C X} (φ : F ⟶ G)
    (h : ∀ i, IsIso (φ.1.app (op (B i)))) : IsIso φ := by
  haveI := TopCat.Opens.coverDense_inducedFunctor hB
  haveI : IsIso (Functor.whiskerLeft (inducedFunctor B).op φ.1) := by
    refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ ?_
    intro i
    exact h i.unop
  exact Functor.IsCoverDense.iso_of_restrict_iso φ this

end S_TopCat_Sheaf_isIso_of_isIso_app_of_isBasis
end P2MW
export P2MW.S_TopCat_Sheaf_isIso_of_isIso_app_of_isBasis (solution)
