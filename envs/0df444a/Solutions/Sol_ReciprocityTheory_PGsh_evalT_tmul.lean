-- Prove2me | solution 1 for ReciprocityTheory.PGsh.evalT_tmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:26:25.775302+00:00
-- url     : https://prove2.me/submissions/70a41d1a-b7c1-4640-bf44-716abae5d8ad

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
variable {M : Type u} [AddCommGroup M] [Module R₀ M]
namespace ReciprocityTheory.PGsh
theorem _root_.solution {A : Type u} [CommRing A] [Algebra R₀ A] (H : M →ₗ[R₀] A) (K : Submodule R₀ A)
    (g : M) (k : K) : evalT H K (g ⊗ₜ k) = H g * k := by
  simp [evalT]
end ReciprocityTheory.PGsh
