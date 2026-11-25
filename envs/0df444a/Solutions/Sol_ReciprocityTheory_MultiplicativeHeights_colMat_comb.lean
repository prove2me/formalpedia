-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.colMat_comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:01:26.840547+00:00
-- url     : https://prove2.me/submissions/1f9953a8-4f2d-42f1-b05f-f7751bcb562e

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegBA

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
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r k : ℕ} (σ : K →+* ℂ)
    (b : Fin k → Fin r → K) (N : Matrix (Fin k) (Fin k) K) :
    colMat σ (fun j => ∑ i, N i j • b i) = colMat σ b * N.map σ := by
  ext a j
  simp only [colMat, Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, map_sum, map_mul]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _
end ReciprocityTheory.MultiplicativeHeights
