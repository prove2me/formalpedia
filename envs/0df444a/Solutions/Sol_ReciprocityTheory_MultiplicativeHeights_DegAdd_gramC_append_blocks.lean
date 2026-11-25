-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.DegAdd.gramC_append_blocks
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:03:43.973996+00:00
-- url     : https://prove2.me/submissions/b4c3a65f-ec61-44cd-abde-e47b591d143a

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
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r k m : ℕ}
    (H : Matrix (Fin r) (Fin r) ℂ) (σ : K →+* ℂ) (b : Fin k → Fin r → K)
    (c : Fin m → Fin r → K) :
    (gramC H σ (Fin.append b c)).submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks (gramC H σ b) (gramX H σ b c) (gramX H σ c b) (gramC H σ c) := by
  ext (i | i) (j | j) <;> simp [gramC, gramX]
end ReciprocityTheory.MultiplicativeHeights.DegAdd
