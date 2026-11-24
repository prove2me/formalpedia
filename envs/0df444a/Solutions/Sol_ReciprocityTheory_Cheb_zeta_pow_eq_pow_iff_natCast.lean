-- Prove2me | solution 1 for ReciprocityTheory.Cheb.zeta_pow_eq_pow_iff_natCast
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:26:56.824402+00:00
-- url     : https://prove2.me/submissions/9b052f1f-d97f-4cfe-bed3-dc1e1526a518

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
theorem _root_.solution {l : ℕ} [NeZero l] {ζ : M} (hζ : IsPrimitiveRoot ζ l) (a b : ℕ) :
    ζ ^ a = ζ ^ b ↔ (a : ZMod l) = b := by
  have hfin : IsOfFinOrder ζ := isOfFinOrder_iff_pow_eq_one.2 ⟨l, NeZero.pos l, hζ.pow_eq_one⟩
  rw [ZMod.natCast_eq_natCast_iff, hζ.eq_orderOf]
  exact hfin.pow_eq_pow_iff_modEq
end ReciprocityTheory.Cheb
