-- Prove2me | solution 1 for ReciprocityTheory.Cheb.pow_apply_zeta_of_apply_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:44:36.394726+00:00
-- url     : https://prove2.me/submissions/15e17a9a-567c-4698-b533-2f5a1febb441

import Mathlib
import Definitions.Def_ReciprocityTheory_Chebotarev_CrossFix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Polynomial
open ReciprocityTheory ReciprocityTheory.Cheb
variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    [IsGalois ℚ K] [IsGalois ℚ M]
namespace ReciprocityTheory.Cheb
theorem _root_.solution {ζ : M} (g : Gal(M/ℚ)) (t : ℕ) (hg : g ζ = ζ ^ t) (m : ℕ) :
    (g ^ m) ζ = ζ ^ (t ^ m) := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, AlgEquiv.mul_apply, hg, map_pow, ih, ← pow_mul, ← pow_succ]
end ReciprocityTheory.Cheb
