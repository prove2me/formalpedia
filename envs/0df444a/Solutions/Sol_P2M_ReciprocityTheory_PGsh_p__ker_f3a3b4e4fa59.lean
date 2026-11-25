-- Prove2me | solution 1 for P2M_ReciprocityTheory_PGsh_p__ker_f3a3b4e4fa59
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:00:06.997013+00:00
-- url     : https://prove2.me/submissions/4657d2e5-c6f1-44d4-a0dd-a771db1dcc50

import Definitions.Def_ReciprocityTheory_DualLattices_NilSurjOfSqZero
import Definitions.Def_ReciprocityTheory_DualLattices_SmKerSurj

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
theorem _root_.solution : ∀ a ∈ (FP.p₁ π Dp.π).ker, (FP.p₂ π Dp.π).1.toLinearMap a ∈ Dp.π.ker := by
  intro a ha
  have ha0 : a.1.1 = 0 := ha
  show Dp.π.1 a.1.2 = 0
  rw [← FP.mem π Dp.π a, ha0, map_zero]
end ReciprocityTheory.PGsh
