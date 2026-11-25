-- Prove2me | solution 1 for P2M_GroundTheory_GroupCoh_isZero_X__of_injective___4a150f60598f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:19:07.013923+00:00
-- url     : https://prove2.me/submissions/bc4e2877-be56-49f2-94e9-a8cc36d0270c

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_SplittingModule
import Definitions.Def_GroundTheory_TateCohomology_CohTrivial
import Definitions.Def_GroundTheory_TateCohomology_ResCores
import Definitions.Def_GroundTheory_TateCohomology_SplittingCohTrivial
import Theorems.Thm_GroundTheory_GroupCoh_eq_zero_of_isZero
import Theorems.Thm_GroundTheory_GroupCoh_isZero_of_forall_eq_zero
import Theorems.Thm_P2M_GroundTheory_GroupCoh___map_g_apply_e86f9a071593
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
theorem _root_.solution (n : ℕ) (h₁ : IsZero (groupCohomology X.X₁ n))
    (hδ : Function.Injective (δ hX n (n + 1) rfl)) : IsZero (groupCohomology X.X₂ n) := by
  refine isZero_of_forall_eq_zero fun x => ?_
  have h1 : map (MonoidHom.id H) X.g n x = 0 :=
    hδ (by rw [δ_map_g_apply hX n (n + 1) rfl, map_zero])
  obtain ⟨w, hw⟩ := exists_map_f_eq hX n x h1
  rw [← hw, eq_zero_of_isZero h₁ w, map_zero]
end GroundTheory.GroupCoh
