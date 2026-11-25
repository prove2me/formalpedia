-- Prove2me | solution 1 for ReciprocityTheory.PGsh.DualPair.isFibreSq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:58:07.079712+00:00
-- url     : https://prove2.me/submissions/43e2b051-9ff6-4e2d-a6b3-768ba2704bc2

import Definitions.Def_ReciprocityTheory_DualLattices_ModuliPointsState
import Definitions.Def_ReciprocityTheory_DualLattices_IsFibreSq
import Theorems.Thm_ReciprocityTheory_PGsh_DualPair_nilSurj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.PGsh
universe u
variable {R₀ : Type u} [CommRing R₀]
open ReciprocityTheory.PGsh.DualPair
variable {R : LAlg R₀} (Dp : DualPair R)
namespace ReciprocityTheory.PGsh.DualPair
theorem _root_.solution : IsFibreSq Dp.p₁L Dp.p₂L Dp.π Dp.π := by
  unfold IsFibreSq
  refine ⟨AlgHom.ext fun q => Dp.fp_eq q, Dp.nilSurj, Dp.nilSurj, fun a b h =>
    ⟨⟨(a, b), h⟩, ⟨rfl, rfl⟩, ?_⟩⟩
  rintro c ⟨h1, h2⟩
  exact Subtype.ext (Prod.ext h1 h2)
end ReciprocityTheory.PGsh.DualPair
