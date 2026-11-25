-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiPt.form_colMat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:55:14.446911+00:00
-- url     : https://prove2.me/submissions/7c4ae0e2-3cb6-4fe2-984d-6471b49968ea

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegI
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegM
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_hGram_eq
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_hermForm_h_eq


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
    (b : Fin k → Fin r → K) (t : Fin k → K) :
    (fun i => S.c (t i)) ⬝ᵥ (hGram S b *ᵥ t) = S.h (colMat b *ᵥ t) (colMat b *ᵥ t) := by
  rw [hGram_eq, hermForm_h_eq]
  simp only [formM]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]
  congr 1
  funext a
  rw [RingHom.map_mulVec]
  rfl
end ReciprocityTheory.MultiplicativeHeights.SemiPt
