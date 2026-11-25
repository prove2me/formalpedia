-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.Smith.VmT_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:36:59.445299+00:00
-- url     : https://prove2.me/submissions/dc6582f2-adc2-4df9-ae8f-9b0fa42abf6c

import Definitions.Def_ReciprocityTheory_DualLattices_UpSmith
import Definitions.Def_ReciprocityTheory_DualLattices_BlockOneMulMulBlockOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.Smith
variable {R : Type} [CommRing R]
namespace ReciprocityTheory.PGsh.Up.Smith
theorem _root_.solution {N n : ℕ} (j0 : Fin (N + 1)) (u : Fin (N + 1) → R) (Y : Matrix (Fin (N + 1)) (Fin n) R)
    (k : Fin (N + 1)) (l : Fin n) :
    ((Vm j0 u)ᵀ * Y) k l = if k = j0 then Y j0 l else Y k l - u k * Y j0 l := by
  classical
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Vm, Matrix.of_apply]
  by_cases hk : k = j0
  · simp [hk]
  · simp only [hk, if_false, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul]
    simp [Finset.sum_ite_eq']
end ReciprocityTheory.PGsh.Up.Smith
