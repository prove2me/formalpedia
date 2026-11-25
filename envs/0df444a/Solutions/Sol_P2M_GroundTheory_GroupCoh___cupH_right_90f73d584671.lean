-- Prove2me | solution 1 for P2M_GroundTheory_GroupCoh___cupH_right_90f73d584671
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:53:37.601172+00:00
-- url     : https://prove2.me/submissions/f5db6939-38f4-4d90-afce-a02c73c60cb4

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupProduct
import Definitions.Def_GroundTheory_TateCohomology_CupConnecting
import Theorems.Thm_GroundTheory_GroupCoh_whiskerLeft_cupCochain
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
theorem _root_.solution (hBX : (X.map (tensorLeft B)).ShortExact) {p q n : ℕ} (h : q + p = n)
    (h' : q + (p + 1) = n + 1) (b : groupCohomology B q) (a : groupCohomology X.X₃ p) :
    δ hBX n (n + 1) rfl (cupH h b a) = (-1 : k) ^ q • cupH h' b (δ hX p (p + 1) rfl a) := by
  refine groupCohomology_induction_on a fun z => ?_
  refine groupCohomology_induction_on b fun w => ?_
  obtain ⟨y, x, hy, hx⟩ := exists_lift_of_cocycle hX z
  rw [δ_π_eq hX z y hy x hx, cupH_π, cupH_π, ← map_smul]
  subst h
  refine δ_π_eq hBX (cupCocycles rfl w z) (cupCochain rfl (iCocycles B q w) y) (fun v => ?_)
    ((-1 : k) ^ q • cupCocycles h' w x) (fun v => ?_)
  · change (B ◁ X.g).hom (cupCochain rfl (iCocycles B q w) y v) =
      iCocycles (B ⊗ X.X₃) (q + p) (cupCocycles rfl w z) v
    rw [iCocycles_cupCocycles, whiskerLeft_cupCochain]
    exact congrArg (fun f => cupCochain rfl (iCocycles B q w) f v) (funext hy)
  · change (B ◁ X.f).hom
        (iCocycles (B ⊗ X.X₁) (q + p + 1) ((-1 : k) ^ q • cupCocycles h' w x) v) =
      (inhomogeneousCochains.d (B ⊗ X.X₂) (q + p)).hom (cupCochain rfl (iCocycles B q w) y) v
    rw [map_smul, Pi.smul_apply, map_smul, iCocycles_cupCocycles, whiskerLeft_cupCochain,
      d_cupCochain, d_iCocycles, cupCochain_zero_left, zero_add, Pi.smul_apply]
    exact congrArg (fun f => (-1 : k) ^ q • cupCochain h' (iCocycles B q w) f v) (funext hx)
end GroundTheory.GroupCoh
