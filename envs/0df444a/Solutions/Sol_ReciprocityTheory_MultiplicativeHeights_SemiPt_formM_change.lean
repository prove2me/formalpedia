-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiPt.formM_change
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:55:08.975192+00:00
-- url     : https://prove2.me/submissions/85beba31-cb81-47d4-917b-8a73ddfc344b

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegG
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegT
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
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (P : Matrix (Fin r) (Fin r) K) (x y : Fin r → K) :
    formM S.c ((P.map S.c)ᵀ * S.G * P) x y = S.h (P *ᵥ x) (P *ᵥ y) := by
  rw [hermForm_h_eq]
  unfold formM
  have e1 : (fun a => S.c ((P *ᵥ x) a)) = (P.map S.c) *ᵥ (fun a => S.c (x a)) := by
    funext a
    exact RingHom.map_mulVec S.c P x a
  rw [e1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
end ReciprocityTheory.MultiplicativeHeights.SemiPt
