-- Prove2me | solution 1 for P2M_ReciprocityTheory_PGsh_BX_tw__r_c0cc6876c9a8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:01:29.658051+00:00
-- url     : https://prove2.me/submissions/0a90de0f-4c59-4225-9bf0-488a3c08d1c2

import Definitions.Def_ReciprocityTheory_DualLattices_NsmulKerZero
import Definitions.Def_ReciprocityTheory_DualLattices_ExistsLimTensor

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
open ReciprocityTheory.PGsh.BX
variable (B : BX R₀) {p : ℕ}
namespace ReciprocityTheory.PGsh.BX
theorem _root_.solution (Tw : ATowerL R₀ p) (n : ℕ) : (Tw.π n).comp (Tw.r' n) = (Tw.r n).comp (Tw.π (n + 1)) := by
  apply Subtype.ext
  apply AlgHom.ext
  intro x
  exact (Tw.r_π n x).symm
end ReciprocityTheory.PGsh.BX
