-- Prove2me | solution 1 for ReciprocityTheory.Cheb.pow_apply_zeta_eq_units_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:52:04.842234+00:00
-- url     : https://prove2.me/submissions/a2a06a93-e438-4b9f-8eb7-97997fe3c30d

import Mathlib
import Definitions.Def_ReciprocityTheory_Chebotarev_CrossFix
import Theorems.Thm_ReciprocityTheory_Cheb_pow_apply_zeta_of_apply_eq_pow
import Theorems.Thm_ReciprocityTheory_Cheb_zeta_pow_eq_pow_iff_natCast

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
theorem _root_.solution {l : ℕ} [NeZero l] {ζ : M} (hζ : IsPrimitiveRoot ζ l) (τ : (ZMod l)ˣ)
    (g : Gal(M/ℚ)) (hgζ : g ζ = ζ ^ (τ : ZMod l).val) (m : ℕ) :
    (g ^ m) ζ = ζ ^ (((τ ^ m : (ZMod l)ˣ) : ZMod l).val) := by
  rw [pow_apply_zeta_of_apply_eq_pow g _ hgζ m, zeta_pow_eq_pow_iff_natCast hζ]
  simp
end ReciprocityTheory.Cheb
