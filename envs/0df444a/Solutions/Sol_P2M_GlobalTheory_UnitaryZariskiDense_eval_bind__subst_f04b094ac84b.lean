-- Prove2me | solution 1 for P2M_GlobalTheory_UnitaryZariskiDense_eval_bind__subst_f04b094ac84b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:32:36.082222+00:00
-- url     : https://prove2.me/submissions/00e945a2-fc76-4794-8972-861c91c137c6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DetGNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryGroupFamilyZariskiDense

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical MvPolynomial
open scoped Matrix ComplexOrder
noncomputable section
open GlobalTheory GlobalTheory.UnitaryZariskiDense
namespace GlobalTheory.UnitaryZariskiDense
theorem _root_.solution {σ τ : Type} (y : τ → ℂ) (f : σ → MvPolynomial τ ℂ) (p : MvPolynomial σ ℂ) :
    eval y (bind₁ f p) = eval (fun v => eval y (f v)) p :=
  eval₂Hom_bind₁ _ _ _ _
end GlobalTheory.UnitaryZariskiDense
