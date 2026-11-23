-- Prove2me | solution 1 for ReciprocityTheory.PGsh.FP.ext
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:17:39.055057+00:00
-- url     : https://prove2.me/submissions/4e724fed-975e-46a1-aa55-89ea8cc21d2c

import Definitions.Def_ReciprocityTheory_DualLattices_ModuliPointsState
import Definitions.Def_ReciprocityTheory_DualLattices_NilSurjOfSqZero

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
variable {R₁ R₂ R : LAlg R₀} (f₁ : LHom R₁ R) (f₂ : LHom R₂ R)
namespace ReciprocityTheory.PGsh
namespace FP
theorem _root_.solution {x y : (FP f₁ f₂ : Type u)} (h1 : x.1.1 = y.1.1) (h2 : x.1.2 = y.1.2) : x = y :=
  Subtype.ext (Prod.ext h1 h2)
end FP
end ReciprocityTheory.PGsh
