-- Prove2me | solution 1 for P2M_Formalism_L2_FormalSeriesBounds_Cart_c0__comb_22429d26040d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:17:26.121915+00:00
-- url     : https://prove2.me/submissions/958263a4-cb0a-4b21-96de-cb57c2ef2116

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeNatCast
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ScaledSecondIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Finset
noncomputable section
variable {C : Type*} [Field C] {V : VF C} {d : ℕ} {I J : Type*}
open Formalism.L2.FormalSeriesBounds.Cart
variable (X : Cart V d I J)
variable {X}
namespace Formalism.L2.FormalSeriesBounds.Cart
theorem _root_.solution {ι : Type*} (s : Finset ι) (x : ι → ℕ → I ⊕ J → C) (co : ι → C) (j : J) :
    X.c0' (∑ k ∈ s, teich V.l (co k) (x k)) j = ∑ k ∈ s, co k ^ V.l * X.c0' (x k) j := by
  simp only [c0', Finset.sum_apply, teich, pow_one, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring
end Formalism.L2.FormalSeriesBounds.Cart
