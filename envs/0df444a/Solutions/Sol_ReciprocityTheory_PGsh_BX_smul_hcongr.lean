-- Prove2me | solution 1 for ReciprocityTheory.PGsh.BX.smul_hcongr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:26:43.705934+00:00
-- url     : https://prove2.me/submissions/f6ecc12a-7201-4ca2-8c03-cee6794c2f67

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
theorem _root_.solution {x₁ x₂ y₁ y₂ : B.G R} (hx : x₁ = x₂) (hy : y₁ = y₂) (l : (R : Type u)ˣ)
    {u₁ : B.P R x₁ y₁} {u₂ : B.P R x₂ y₂} (hu : HEq u₁ u₂) :
    HEq (B.smul l u₁) (B.smul l u₂) := by
  subst hx hy; cases eq_of_heq hu; rfl
end ReciprocityTheory.PGsh.BX
