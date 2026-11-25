-- Prove2me | solution 1 for P2M_ReciprocityTheory_PGsh_p__comp____99b01a1e79c6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:59:59.005799+00:00
-- url     : https://prove2.me/submissions/ba5991a0-54ca-489f-8604-1dd4afbad78a

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
theorem _root_.solution : (FP.p₂ π Dp.π).comp (ι₁ π Dp) = Dp.σ.comp π := Subtype.ext (AlgHom.ext fun _ => rfl)
end ReciprocityTheory.PGsh
