-- Prove2me | solution 1 for ReciprocityTheory.PGsh.BX.tw_qr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:18:15.067834+00:00
-- url     : https://prove2.me/submissions/3d142e89-5ff4-42b9-8e57-42918cb891a1

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
theorem _root_.solution (Tw : ATowerL R₀ p) (n : ℕ) : (Tw.r n).comp (Tw.q (n + 1)) = Tw.q n := by
  apply Subtype.ext
  apply AlgHom.ext
  intro x
  exact Tw.r_q n x
end ReciprocityTheory.PGsh.BX
