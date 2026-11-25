-- Prove2me | solution 1 for P2M_ReciprocityTheory_PGsh_sm_comp____a42742269e01
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:00:21.122598+00:00
-- url     : https://prove2.me/submissions/bccd46d9-6180-4a10-996e-39778fd324e1

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
variable {R' R : LAlg R₀} (π : LHom R' R) (Dp : DualPair R)
namespace ReciprocityTheory.PGsh
theorem _root_.solution {ξ : (R' : Type u)} (hsurj : Function.Surjective π.1)
    (hker : RingHom.ker π.1 = Ideal.span {ξ}) (hsq : ξ * ξ = 0) :
    (sm π Dp ξ hsurj hker hsq).comp (ι₁ π Dp) = LHom.id R' := by
  apply Subtype.ext
  apply AlgHom.ext
  intro t
  show t + ell π ξ hsurj (Dp.κ (Dp.σ.1 (π.1 t))) = t
  rw [Dp.κ_σ, ell_zero hsurj hker hsq, add_zero]
end ReciprocityTheory.PGsh
