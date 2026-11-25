-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiPt.gramC_posDef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:16:41.310925+00:00
-- url     : https://prove2.me/submissions/68a3d129-3d6f-4b1e-a86d-cc05e4901472

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegE
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_gramC_eq
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_embMat_injective

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
    (H : Matrix (Fin r) (Fin r) ℂ) (hH : H.PosDef) (σ : K →+* ℂ) (b : Fin k → Fin r → K)
    (hli : LinearIndependent K b) : (gramC H σ b).PosDef := by
  rw [gramC_eq]
  exact hH.conjTranspose_mul_mul_same (embMat_injective S σ b hli)
end ReciprocityTheory.MultiplicativeHeights.SemiPt
