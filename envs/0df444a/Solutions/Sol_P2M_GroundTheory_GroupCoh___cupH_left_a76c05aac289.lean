-- Prove2me | solution 1 for P2M_GroundTheory_GroupCoh___cupH_left_a76c05aac289
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:54:24.712929+00:00
-- url     : https://prove2.me/submissions/5db69b92-6587-4cf3-9e58-4dfecb2a6abc

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupProduct
import Definitions.Def_GroundTheory_TateCohomology_CupConnecting
import Theorems.Thm_GroundTheory_GroupCoh_whiskerRight_cupCochain
import Theorems.Thm_P2M_GroundTheory_GroupCoh_____eq_9cd1eeda1d2f
import Theorems.Thm_GroundTheory_GroupCoh_exists_lift_of_cocycle
import Theorems.Thm_GroundTheory_GroupCoh_d_cupCochain
import Theorems.Thm_P2M_GroundTheory_GroupCoh_cupH___fa07882c353c


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
universe u
open CategoryTheory MonoidalCategory TensorProduct groupCohomology Limits
open GroundTheory GroundTheory.GroupCoh
variable {k G : Type u} [CommRing k] [Group G]
variable {X : ShortComplex (Rep k G)} (hX : X.ShortExact)
variable (B : Rep k G)
namespace GroundTheory.GroupCoh
theorem _root_.solution (hXB : (X.map (tensorRight B)).ShortExact) {p q n : ℕ} (h : p + q = n)
    (h' : p + 1 + q = n + 1) (a : groupCohomology X.X₃ p) (b : groupCohomology B q) :
    δ hXB n (n + 1) rfl (cupH h a b) = cupH h' (δ hX p (p + 1) rfl a) b := by
  refine groupCohomology_induction_on a fun z => ?_
  refine groupCohomology_induction_on b fun w => ?_
  obtain ⟨y, x, hy, hx⟩ := exists_lift_of_cocycle hX z
  rw [δ_π_eq hX z y hy x hx, cupH_π, cupH_π]
  subst h
  refine δ_π_eq hXB (cupCocycles rfl z w) (cupCochain rfl y (iCocycles B q w)) (fun v => ?_)
    (cupCocycles h' x w) (fun v => ?_)
  · change (X.g ▷ B).hom (cupCochain rfl y (iCocycles B q w) v) =
      iCocycles (X.X₃ ⊗ B) (p + q) (cupCocycles rfl z w) v
    rw [iCocycles_cupCocycles, whiskerRight_cupCochain]
    exact congrArg (fun f => cupCochain rfl f (iCocycles B q w) v) (funext hy)
  · change (X.f ▷ B).hom (iCocycles (X.X₁ ⊗ B) (p + q + 1) (cupCocycles h' x w) v) =
      (inhomogeneousCochains.d (X.X₂ ⊗ B) (p + q)).hom (cupCochain rfl y (iCocycles B q w)) v
    rw [iCocycles_cupCocycles, whiskerRight_cupCochain, d_cupCochain, d_iCocycles,
      cupCochain_zero_right, smul_zero, add_zero]
    exact congrArg (fun f => cupCochain h' f (iCocycles B q w) v) (funext hx)
end GroundTheory.GroupCoh
