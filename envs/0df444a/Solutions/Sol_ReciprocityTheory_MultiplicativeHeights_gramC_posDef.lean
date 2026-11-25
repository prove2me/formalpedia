-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.gramC_posDef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:20:18.542508+00:00
-- url     : https://prove2.me/submissions/1247cc01-c869-4953-9c4e-34cb0396106b

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegBA
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_gramC_eq_colMat
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_colMat_mulVec_injective

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
    (hH : H.PosDef) (hb : LinearIndependent K b) : (gramC H σ b).PosDef := by
  rw [gramC_eq_colMat]
  exact hH.conjTranspose_mul_mul_same (colMat_mulVec_injective σ b hb)
end ReciprocityTheory.MultiplicativeHeights
