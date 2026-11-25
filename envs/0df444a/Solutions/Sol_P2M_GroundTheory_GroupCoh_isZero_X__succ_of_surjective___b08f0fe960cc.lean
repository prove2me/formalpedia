-- Prove2me | solution 1 for P2M_GroundTheory_GroupCoh_isZero_X__succ_of_surjective___b08f0fe960cc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:19:08.43196+00:00
-- url     : https://prove2.me/submissions/b77fd71d-bed5-404a-8fcc-f34d670d038f

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_SplittingModule
import Definitions.Def_GroundTheory_TateCohomology_CohTrivial
import Definitions.Def_GroundTheory_TateCohomology_ResCores
import Definitions.Def_GroundTheory_TateCohomology_SplittingCohTrivial
import Theorems.Thm_GroundTheory_GroupCoh_eq_zero_of_isZero
import Theorems.Thm_GroundTheory_GroupCoh_isZero_of_forall_eq_zero
import Theorems.Thm_P2M_GroundTheory_GroupCoh_map_f___apply_291461d878e9
import Theorems.Thm_GroundTheory_GroupCoh_exists_map_f_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory Limits groupCohomology Rep
open GroundTheory GroundTheory.GroupCoh
universe u
variable {k H : Type u} [CommRing k] [Group H] {X : ShortComplex (Rep.{u} k H)} (hX : X.ShortExact)
include hX
namespace GroundTheory.GroupCoh
theorem _root_.solution (n : ℕ) (h₃ : IsZero (groupCohomology X.X₃ (n + 1)))
    (hδ : Function.Surjective (δ hX n (n + 1) rfl)) : IsZero (groupCohomology X.X₂ (n + 1)) := by
  refine isZero_of_forall_eq_zero fun x => ?_
  obtain ⟨w, hw⟩ := exists_map_f_eq hX (n + 1) x (eq_zero_of_isZero h₃ _)
  obtain ⟨z, rfl⟩ := hδ w
  rw [← hw, map_f_δ_apply hX n (n + 1) rfl z]
end GroundTheory.GroupCoh
