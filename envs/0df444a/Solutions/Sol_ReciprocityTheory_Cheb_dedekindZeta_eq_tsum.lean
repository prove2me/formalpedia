-- Prove2me | solution 1 for ReciprocityTheory.Cheb.dedekindZeta_eq_tsum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:54:06.897813+00:00
-- url     : https://prove2.me/submissions/7e17039c-cbc9-4008-9795-cb148eaeec8d

import Definitions.Def_ReciprocityTheory_Chebotarev_NZIdeal
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
import Theorems.Thm_ReciprocityTheory_Cheb_dedekindZeta_eq_idealZetaR
import Theorems.Thm_ReciprocityTheory_Cheb_hasSum_absNorm_rpow_ideal

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
theorem _root_.solution (E : Type) [Field E] [NumberField E] {s : ℝ} (hs : 1 < s) :
    dedekindZeta E s = ∑' a : NZIdeal E, ((Ideal.absNorm a.1 : ℕ) : ℂ) ^ (-(s : ℂ)) := by
  have hsupp : Function.support (fun a : Ideal (𝓞 E) => ((Ideal.absNorm a : ℕ) : ℝ) ^ (-s)) ⊆
      {a | a ≠ ⊥} := by
    intro a ha hbot
    apply ha
    have hb : a = ⊥ := by simpa using hbot
    simp [hb, Real.zero_rpow (neg_ne_zero.mpr (zero_lt_one.trans hs).ne')]
  have h1 : ∑' a : NZIdeal E, ((Ideal.absNorm a.1 : ℕ) : ℝ) ^ (-s) = idealZetaR E s := by
    rw [← (hasSum_absNorm_rpow_ideal E hs).tsum_eq]
    exact tsum_subtype_eq_of_support_subset hsupp
  rw [dedekindZeta_eq_idealZetaR E hs, ← h1, Complex.ofReal_tsum]
  refine tsum_congr fun a ↦ ?_
  rw [Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_neg, Complex.ofReal_natCast]
end ReciprocityTheory.Cheb
