-- Prove2me | solution 1 for P2M_GlobalTheory_range_subset_range_equalizer___aeb7241b0453
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:34:17.101715+00:00
-- url     : https://prove2.me/submissions/bafce225-ddd2-4c4e-a378-04121845a759

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian

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
theorem _root_.solution {X T Z : Scheme.{u}} {a b : T ⟶ X} (j : Z ⟶ T)
    (hj : j ≫ a = j ≫ b) : Set.range j ⊆ Set.range (equalizer.ι a b) := by
  rintro _ ⟨z, rfl⟩
  exact ⟨equalizer.lift j hj z, by rw [← Scheme.Hom.comp_apply, equalizer.lift_ι]⟩
end GlobalTheory
