-- Prove2me | solution 1 for P2M_GroundTheory_GroupCoh_____eq_9cd1eeda1d2f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:51:31.499885+00:00
-- url     : https://prove2.me/submissions/c4ab484c-bc7f-4a9a-95f8-cb0e82cd0810

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupProduct
import Definitions.Def_GroundTheory_TateCohomology_CupConnecting
import Theorems.Thm_GroundTheory_GroupCoh_cupCochainsTensor_tmul
import Theorems.Thm_P2M_GroundTheory_GroupCoh_cup__apply_a78771e4f336
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.GroupCoh.cupCochainsTensor_tmul
attribute [local simp] P2M_GroundTheory_GroupCoh_cup__apply_a78771e4f336



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
universe u
open CategoryTheory MonoidalCategory TensorProduct groupCohomology Limits
open GroundTheory GroundTheory.GroupCoh
variable {k G : Type u} [CommRing k] [Group G]
variable {X : ShortComplex (Rep k G)} (hX : X.ShortExact)
include hX
namespace GroundTheory.GroupCoh
theorem _root_.solution {p : ℕ} (z : cocycles X.X₃ p) (y : (Fin p → G) → X.X₂)
    (hy : ∀ v, X.g.hom (y v) = iCocycles X.X₃ p z v) (x : cocycles X.X₁ (p + 1))
    (hx : ∀ v, X.f.hom (iCocycles X.X₁ (p + 1) x v) = (inhomogeneousCochains.d X.X₂ p).hom y v) :
    δ hX p (p + 1) rfl (π X.X₃ p z) = π X.X₁ (p + 1) x := by
  have h1 := δ_apply hX rfl (iCocycles X.X₃ p z) (by simpa using d_iCocycles z) y
    (funext hy) (iCocycles X.X₁ (p + 1) x) (funext fun v => by simpa using hx v)
  have e1 : cocyclesMk (iCocycles X.X₃ p z) (d_iCocycles z) = z := cocycles_ext (iCocycles_mk _ _)
  rw [e1] at h1
  rw [h1]
  congr 1
  exact cocycles_ext (iCocycles_mk _ _)
end GroundTheory.GroupCoh
