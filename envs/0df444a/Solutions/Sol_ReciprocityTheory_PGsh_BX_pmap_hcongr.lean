-- Prove2me | solution 1 for ReciprocityTheory.PGsh.BX.pmap_hcongr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:16:53.059591+00:00
-- url     : https://prove2.me/submissions/79239251-f8ba-4346-a109-7d1f9ef50f9d

import Definitions.Def_ReciprocityTheory_DualLattices_SqZeroOfSpan
import Definitions.Def_ReciprocityTheory_DualLattices_InstAddCommMonoidFibreFst

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
open ReciprocityTheory.PGsh.BX
variable (B : BX R₀) {R : LAlg R₀}
namespace ReciprocityTheory.PGsh.BX
theorem _root_.solution {S : LAlg R₀} (f : LHom R S) {x₁ x₂ y₁ y₂ : B.G R} (hx : x₁ = x₂)
    (hy : y₁ = y₂) {u₁ : B.P R x₁ y₁} {u₂ : B.P R x₂ y₂} (hu : HEq u₁ u₂) :
    HEq (B.pmap f u₁) (B.pmap f u₂) := by
  subst hx hy; cases eq_of_heq hu; rfl
end ReciprocityTheory.PGsh.BX
