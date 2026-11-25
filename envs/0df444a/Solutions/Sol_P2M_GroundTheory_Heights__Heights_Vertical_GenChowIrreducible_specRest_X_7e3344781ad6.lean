-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_GenChowIrreducible_specRest_X_7e3344781ad6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:23:11.591247+00:00
-- url     : https://prove2.me/submissions/b50fe22b-b8d4-4ed6-8774-fc846f8969f9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PGenChowIrreducible

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
open GroundTheory.Heights₂.Heights.Vertical.GenChowIrreducible
variable {n e : ℕ}
namespace GroundTheory.Heights₂.Heights.Vertical.GenChowIrreducible
theorem _root_.solution {k : Type*} [Field k] (f : MvPolynomial (Fin (e + 1) × Fin n) k) :
    specRest (algebraMap k (MvPolynomial (Par e n) k)) f X =
      sumAlgEquiv k (Fin n) (Par e n) (rename (parVar e n) f) := by
  unfold specRest
  rw [MvPolynomial.algebraMap_eq]
  induction f using MvPolynomial.induction_on with
  | C a => simp [sumAlgEquiv_C_inl]
  | add p q hp hq => simp [eval₂_add, hp, hq]
  | mul_X p ij hp =>
    obtain ⟨i, j⟩ := ij
    induction i using Fin.cases <;>
      simp [eval₂_mul, hp, parVar, sumAlgEquiv_X_inl, sumAlgEquiv_X_inr]
end GroundTheory.Heights₂.Heights.Vertical.GenChowIrreducible
