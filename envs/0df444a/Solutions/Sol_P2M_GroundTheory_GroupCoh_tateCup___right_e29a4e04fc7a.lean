-- Prove2me | solution 1 for P2M_GroundTheory_GroupCoh_tateCup___right_e29a4e04fc7a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:38:16.680847+00:00
-- url     : https://prove2.me/submissions/e2c6a8be-18b2-44a8-9f04-520929b8ca18

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupTateShift
import Definitions.Def_GroundTheory_TateCohomology_CupTate
import Theorems.Thm_GroundTheory_GroupCoh_tateCup_connecting_right


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory MonoidalCategory groupCohomology
open GroundTheory GroundTheory.GroupCoh
universe u
variable {k G : Type u} [CommRing k] [Group G] [Fintype G]
namespace GroundTheory.GroupCoh
theorem _root_.solution {E : ShortComplex (Rep.{u} k G)} (hE : E.ShortExact) (A : Rep.{u} k G)
    (hAE : (E.map (tensorLeft A)).ShortExact) (p q r : ℤ) (h : p + q = r)
    (a : tateCohomology A p) (b : tateCohomology E.X₃ q) :
    (TateCohomology.δ hAE r).hom (tateCup p q A E.X₃ r h a b) =
      p.negOnePow • tateCup p (q + 1) A E.X₁ (r + 1) (by omega) a ((TateCohomology.δ hE q).hom b) := by
  rw [Units.smul_def, ← Int.cast_smul_eq_zsmul k]
  exact tateCup_connecting_right _ p q rfl hE A hAE r h a b
end GroundTheory.GroupCoh
