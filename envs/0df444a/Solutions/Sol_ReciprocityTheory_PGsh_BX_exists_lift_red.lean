-- Prove2me | solution 1 for ReciprocityTheory.PGsh.BX.exists_lift_red
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:16:31.756338+00:00
-- url     : https://prove2.me/submissions/9c6365c9-fa1f-4761-b6e0-b04ae5c09867

import Definitions.Def_ReciprocityTheory_DualLattices_InstAddCommMonoidFibreFst
import Definitions.Def_ReciprocityTheory_DualLattices_NilSurjOfSqZero
import Definitions.Def_ReciprocityTheory_DualLattices_NsmulTensorEqZero
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
open ReciprocityTheory.PGsh.BX
variable (B : BX R₀) {R : LAlg R₀} (Dp : DualPair R)
namespace ReciprocityTheory.PGsh.BX
theorem _root_.solution {x y : B.G Dp.D} {x₀ y₀ : B.G R} (hx : B.map Dp.π x = x₀)
    (hy : B.map Dp.π y = y₀) (e : B.P R x₀ y₀) : ∃ u : B.P Dp.D x y, HEq (B.pmap Dp.π u) e := by
  subst hx hy
  obtain ⟨u0⟩ := B.nonempty Dp.D x y
  obtain ⟨l, hl, -⟩ := B.trans (B.pmap Dp.π u0) e
  refine ⟨B.smul (Units.map (Dp.σ.1 : (R : Type u) →* (Dp.D : Type u)) l) u0, ?_⟩
  rw [B.pmap_smul]
  have h1 : Units.map (Dp.π.1 : (Dp.D : Type u) →* (R : Type u))
      (Units.map (Dp.σ.1 : (R : Type u) →* (Dp.D : Type u)) l) = l := by
    ext
    simp [Dp.sect]
  rw [h1, hl]
end ReciprocityTheory.PGsh.BX
