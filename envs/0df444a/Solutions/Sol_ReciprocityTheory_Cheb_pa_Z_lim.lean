-- Prove2me | solution 1 for ReciprocityTheory.Cheb.pa_Z_lim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:07:39.882464+00:00
-- url     : https://prove2.me/submissions/3437e8df-869d-493b-bfac-a8664ff593a0

import Definitions.Def_ReciprocityTheory_Chebotarev_CasimirPowerSurjectiveSymmetric
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerLim
import Definitions.Def_ReciprocityTheory_Chebotarev_PrimeAsymp
import Theorems.Thm_ReciprocityTheory_Cheb_pa_cpow_eq
import Theorems.Thm_ReciprocityTheory_Cheb_dedekindZeta_eq_tsum


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
theorem _root_.solution (E : Type) [Field E] [NumberField E] :
    Tendsto (fun s : ℝ => (s - 1) * ∑' a : NZIdeal E, ((Ideal.absNorm a.1 : ℕ) : ℝ) ^ (-s))
      (𝓝[>] 1) (𝓝 (dedekindZeta_residue E)) := by
  have h := (Complex.continuous_re.tendsto _).comp (tendsto_sub_one_mul_dedekindZeta_nhdsGT E)
  simp only [Complex.ofReal_re] at h
  refine h.congr' ?_
  refine eventually_nhdsWithin_of_forall fun s (hs : 1 < s) => ?_
  simp only [Function.comp_apply]
  rw [dedekindZeta_eq_tsum E hs]
  have e : (∑' a : NZIdeal E, ((Ideal.absNorm a.1 : ℕ) : ℂ) ^ (-(s : ℂ))) =
      ((∑' a : NZIdeal E, ((Ideal.absNorm a.1 : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    exact tsum_congr fun a => pa_cpow_eq _ _
  rw [e, ← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_mul, Complex.ofReal_re]
end ReciprocityTheory.Cheb
