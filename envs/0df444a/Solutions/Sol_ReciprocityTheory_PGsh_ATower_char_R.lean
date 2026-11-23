-- Prove2me | solution 1 for ReciprocityTheory.PGsh.ATower.char_R
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:42:19.07609+00:00
-- url     : https://prove2.me/submissions/16a3616e-7336-46c1-ba2d-ae305f8d24a5

import Definitions.Def_ReciprocityTheory_DualLattices_ExistsLimTensor
import Definitions.Def_ReciprocityTheory_DualLattices_CharR

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
namespace ReciprocityTheory.PGsh
namespace ATower
theorem _root_.solution {p : ℕ} (Tw : ATower R₀ p) (n : ℕ) : ((p ^ (n + 1) : ℕ) : (Tw.R n : Type u)) = 0 := by
  have h := congrArg (Tw.π n).1 (Tw.char n)
  rwa [map_natCast, map_zero] at h
end ATower
end ReciprocityTheory.PGsh
