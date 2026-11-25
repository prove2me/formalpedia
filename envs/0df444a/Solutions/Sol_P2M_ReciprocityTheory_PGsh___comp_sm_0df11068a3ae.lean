-- Prove2me | solution 1 for P2M_ReciprocityTheory_PGsh___comp_sm_0df11068a3ae
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:59:56.401027+00:00
-- url     : https://prove2.me/submissions/1e1d57aa-fc1b-480c-b40e-721f238a3a0d

import Definitions.Def_ReciprocityTheory_DualLattices_NilSurjOfSqZero
import Definitions.Def_ReciprocityTheory_DualLattices_SmKerSurj
import Theorems.Thm_ReciprocityTheory_PGsh_FP_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct
open ReciprocityTheory ReciprocityTheory.PGsh
universe u
variable {R₀ : Type u} [CommRing R₀]
variable {R' R : LAlg R₀} (π : LHom R' R) (Dp : DualPair R) (ξ : (R' : Type u))
  (hsurj : Function.Surjective π.1) (hker : RingHom.ker π.1 = Ideal.span {ξ}) (hsq : ξ * ξ = 0)
namespace ReciprocityTheory.PGsh
theorem _root_.solution : π.comp (sm π Dp ξ hsurj hker hsq) = π.comp (FP.p₁ π Dp.π) := by
  apply Subtype.ext
  apply AlgHom.ext
  intro x
  show π.1 (x.1.1 + ell π ξ hsurj (Dp.κ x.1.2)) = π.1 x.1.1
  rw [map_add, ell_π hsurj hker, add_zero]
end ReciprocityTheory.PGsh
