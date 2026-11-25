-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_SecAlgFinite_transVar_injective_ef04c1d79d51
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:24:08.25294+00:00
-- url     : https://prove2.me/submissions/c12c8c2f-c35f-4870-8c5a-8df838f3054a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecAlgFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.SecAlgFinite
variable {k E : Type} [Field k] [Field E] [Algebra k E] {n e : ℕ}
namespace GroundTheory.Heights₂.Heights.Vertical.SecAlgFinite
theorem _root_.solution (m : Fin n) :
    Function.Injective (aeval (R := k) (transVar (k := k) (e := e) m)) := by
  have h : (aeval (R := k) (transVarInv (k := k) (e := e) m)).comp (aeval (R := k) (transVar m)) =
      AlgHom.id k _ := by
    apply MvPolynomial.algHom_ext
    rintro ⟨i, j⟩
    induction i using Fin.cases with
    | zero => by_cases hj : j = m <;> simp [transVar, transVarInv, hj]
    | succ i => simp [transVar, transVarInv]
  refine Function.LeftInverse.injective (g := aeval (R := k) (transVarInv m)) fun p => ?_
  simpa using DFunLike.congr_fun h p
end GroundTheory.Heights₂.Heights.Vertical.SecAlgFinite
