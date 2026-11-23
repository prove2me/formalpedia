-- Prove2me | solution 1 for P2M_GlobalTheory_eq_of_range_equalizer___eq_univ_5724cbc41fd4
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:28.191114+00:00
-- url     : https://prove2.me/submissions/6f1dd88a-60e8-42b8-b775-17a6de7497dc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Theorems.Thm_P2M_GlobalTheory_isOpenImmersion_equalizer___of_unramified_d71f398b7582

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {X S T : Scheme.{u}} (f : X ⟶ S)
    [FormallyUnramified f] [LocallyOfFiniteType f] {a b : T ⟶ X} (hab : a ≫ f = b ≫ f)
    (h : Set.range (equalizer.ι a b) = Set.univ) : a = b := by
  have := isOpenImmersion_equalizer_ι_of_unramified f hab
  have : IsIso (equalizer.ι a b) :=
    isIso_of_isOpenImmersion_of_opensRange_eq_top _ (Opens.ext h)
  rw [← cancel_epi (equalizer.ι a b), equalizer.condition]
end GlobalTheory
