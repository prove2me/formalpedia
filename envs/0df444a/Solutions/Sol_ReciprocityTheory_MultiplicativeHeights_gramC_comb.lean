-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.gramC_comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:32:03.892804+00:00
-- url     : https://prove2.me/submissions/68907a1e-5eaa-4a45-aa6e-1d832015814b

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegBA
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_gramC_eq_colMat
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_colMat_comb

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
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (H : Matrix (Fin r) (Fin r) ℂ) (σ : K →+* ℂ) (b : Fin k → Fin r → K)
    (N : Matrix (Fin k) (Fin k) K) :
    gramC H σ (fun j => ∑ i, N i j • b i) = (N.map σ)ᴴ * gramC H σ b * N.map σ := by
  rw [gramC_eq_colMat, gramC_eq_colMat, colMat_comb, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]
end ReciprocityTheory.MultiplicativeHeights
