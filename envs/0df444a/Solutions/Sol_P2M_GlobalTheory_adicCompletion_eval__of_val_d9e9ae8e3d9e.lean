-- Prove2me | solution 1 for P2M_GlobalTheory_adicCompletion_eval__of_val_d9e9ae8e3d9e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:34:29.222058+00:00
-- url     : https://prove2.me/submissions/5f1381e0-e603-4b7e-bf18-88b373181a88

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsInjectiveAdicCompletionMapOfFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {R : Type} [CommRing R] (I : Ideal R) (x : AdicCompletion I R)
    {n : ℕ} (d : R) (hd : x.val n = Submodule.Quotient.mk d) :
    AdicCompletion.evalₐ I n x = Ideal.Quotient.mk (I ^ n) d := by
  rw [← AdicCompletion.factor_eval_eq_evalₐ I x (by simp), AdicCompletion.eval_apply]
  erw [hd]
  rfl
end GlobalTheory
