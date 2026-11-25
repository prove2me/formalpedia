-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sc_gramC_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:06:03.981989+00:00
-- url     : https://prove2.me/submissions/8d174843-817c-456a-a2b7-8683e8408cc6

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
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (H : Matrix (Fin r) (Fin r) ℂ) (σ : K →+* ℂ) (b : Fin k → Fin r → K) :
    gramC H σ b = (embCols σ b)ᴴ * H * embCols σ b := by
  ext i j
  simp only [gramC, embCols, embVec, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, dotProduct,
    Matrix.mulVec, Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
end ReciprocityTheory.MultiplicativeHeights
