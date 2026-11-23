-- Prove2me | solution 1 for ReciprocityTheory.PGsh.evalT_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:33:23.48916+00:00
-- url     : https://prove2.me/submissions/eec84b55-8db5-45bd-bae5-47039cd44865

import Definitions.Def_ReciprocityTheory_DualLattices_ModuliPointsState
import Definitions.Def_ReciprocityTheory_DualLattices_NilSurjOfSqZero
import Theorems.Thm_ReciprocityTheory_PGsh_evalT_tmul
import Theorems.Thm_ReciprocityTheory_PGsh_evalT_add
import Theorems.Thm_ReciprocityTheory_PGsh_evalT_zero

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
theorem _root_.solution {A : Type u} [CommRing A] [Algebra R₀ A] (H : M →ₗ[R₀] A) (I : Ideal A)
    (Y : M ⊗[R₀] (I.restrictScalars R₀)) : evalT H (I.restrictScalars R₀) Y ∈ I := by
  induction Y using TensorProduct.induction_on with
  | zero =>
    rw [evalT_zero]
    exact I.zero_mem
  | tmul g k =>
    rw [evalT_tmul]
    exact I.mul_mem_left _ k.2
  | add Y Y' hY hY' =>
    rw [evalT_add]
    exact I.add_mem hY hY'
end ReciprocityTheory.PGsh
