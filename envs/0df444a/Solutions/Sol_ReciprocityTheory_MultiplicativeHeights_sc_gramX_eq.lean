-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sc_gramX_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:06:07.6146+00:00
-- url     : https://prove2.me/submissions/940453c1-6a5e-40da-b500-f99899566ce8

import Definitions.Def_ReciprocityTheory_SemistableReduction_LatSemiSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiContractA
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiContractB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix NumberField
open scoped ComplexOrder
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r k m : ℕ}
    (H : Matrix (Fin r) (Fin r) ℂ) (σ : K →+* ℂ) (b : Fin k → Fin r → K) (c : Fin m → Fin r → K) :
    gramX H σ b c = (embCols σ b)ᴴ * H * embCols σ c := by
  ext i j
  simp only [gramX, embCols, embVec, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, dotProduct,
    Matrix.mulVec, Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
end ReciprocityTheory.MultiplicativeHeights
