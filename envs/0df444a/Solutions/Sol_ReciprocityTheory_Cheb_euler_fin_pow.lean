-- Prove2me | solution 1 for ReciprocityTheory.Cheb.euler_fin_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:41:47.333265+00:00
-- url     : https://prove2.me/submissions/5347647c-be44-48a0-bab2-7533964661b2

import Definitions.Def_ReciprocityTheory_Chebotarev_EulerFac
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerFin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Filter Topology
open ReciprocityTheory ReciprocityTheory.Cheb
namespace ReciprocityTheory.Cheb
theorem _root_.solution {E : Type} [Field E] [NumberField E] (f : Ideal (𝓞 E) → ℂ) (hf1 : f 1 = 1)
    (hmul : ∀ a b : Ideal (𝓞 E), f (a * b) = f a * f b) (a : Ideal (𝓞 E)) (k : ℕ) :
    f (a ^ k) = f a ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, hf1]
  | succ k ih => rw [pow_succ, hmul, ih, pow_succ]
end ReciprocityTheory.Cheb
