-- Prove2me | solution 1 for ReciprocityTheory.PGsh.BX.nsmul_tensor_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:03:38.851877+00:00
-- url     : https://prove2.me/submissions/81157f74-3f77-4965-acf1-1c7c760facff

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
theorem _root_.solution {A : Type u} [CommRing A] [Algebra R₀ A] {N : ℕ}
    (hN : (N : A) = 0) (K : Submodule R₀ A) (Y : B.gg ⊗[R₀] K) : N • Y = 0 := by
  induction Y using TensorProduct.induction_on with
  | zero => exact smul_zero _
  | tmul g k =>
    rw [← Nat.cast_smul_eq_nsmul R₀, ← TensorProduct.tmul_smul]
    have hk : ((N : R₀) • k) = 0 := by
      ext
      simp [Algebra.smul_def, hN]
    rw [hk, TensorProduct.tmul_zero]
  | add x y hx hy => rw [smul_add, hx, hy, add_zero]
end ReciprocityTheory.PGsh.BX
