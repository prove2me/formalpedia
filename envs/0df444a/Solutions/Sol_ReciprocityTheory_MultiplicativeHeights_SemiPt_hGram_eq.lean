-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiPt.hGram_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:18:56.908901+00:00
-- url     : https://prove2.me/submissions/857b3d6c-9c8b-4397-a79e-a4ce41eadad1

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegI
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegM

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.SemiPt
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder
namespace ReciprocityTheory.MultiplicativeHeights.SemiPt
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r k : ℕ} (S : HermForm K r)
    (b : Fin k → Fin r → K) : hGram S b = ((colMat b).map S.c)ᵀ * S.G * colMat b := by
  ext i j
  simp only [hGram, HermForm.h, colMat, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
end ReciprocityTheory.MultiplicativeHeights.SemiPt
