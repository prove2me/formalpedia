-- Prove2me | solution 1 for P2M_GlobalTheory_UnipotentInvariant_eval_bind___d799cbbaf6da
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:21:02.68859+00:00
-- url     : https://prove2.me/submissions/2c50ab65-b8c2-4020-8886-b5e7260d98b2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ProdLeadMinorDiagonal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
open GlobalTheory
open GlobalTheory.UnipotentInvariant
variable {K : Type*} [Field K] {p : ℕ}
variable {σ : Type*} [DecidableEq σ]
omit [DecidableEq σ]
namespace GlobalTheory.UnipotentInvariant
theorem _root_.solution (y : σ → K) (g : σ → MvPolynomial σ K) (P : MvPolynomial σ K) :
    eval y (bind₁ g P) = eval (fun s => eval y (g s)) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P s hP => simp [hP]
end GlobalTheory.UnipotentInvariant
