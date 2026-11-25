-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.DegAdd.gramC_posDef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:33:08.394378+00:00
-- url     : https://prove2.me/submissions/5fa78fcb-db76-460d-96bf-914d0ac69bf1

import Definitions.Def_ReciprocityTheory_SemistableReduction_LatSemiSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_EmbMatMulVecInjective
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_DegAdd_gramC_eq_mul
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_DegAdd_embMat_mulVec_injective

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
    (H : Matrix (Fin r) (Fin r) ℂ) (σ : K →+* ℂ) {v : Fin k → Fin r → K} (hH : H.PosDef)
    (hv : LinearIndependent K v) : (gramC H σ v).PosDef := by
  rw [gramC_eq_mul]
  exact hH.conjTranspose_mul_mul_same (embMat_mulVec_injective σ hv)
end ReciprocityTheory.MultiplicativeHeights.DegAdd
