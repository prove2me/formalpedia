-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.DegAdd.gramC_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:17:09.313612+00:00
-- url     : https://prove2.me/submissions/b8c5c24e-5de4-4e6f-9d9c-482d66f98f24

import Definitions.Def_ReciprocityTheory_SemistableReduction_LatSemiSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_EmbMatMulVecInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open ReciprocityTheory.MultiplicativeHeights.DegAdd
open Matrix NumberField
open scoped ComplexOrder
namespace ReciprocityTheory.MultiplicativeHeights.DegAdd
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (H : Matrix (Fin r) (Fin r) ℂ) (σ : K →+* ℂ) (v : Fin k → Fin r → K) :
    gramC H σ v = (embMat σ v)ᴴ * H * embMat σ v := by
  ext i j
  simp only [gramC, embMat, embVec, Matrix.of_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, dotProduct, Matrix.mulVec, Pi.star_apply, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by ring
end ReciprocityTheory.MultiplicativeHeights.DegAdd
