-- Prove2me | solution 1 for ReciprocityTheory.Cheb.real_euler
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:06:18.639719+00:00
-- url     : https://prove2.me/submissions/d633917c-8cb0-4c41-93f6-9fa149879017

import Definitions.Def_ReciprocityTheory_Chebotarev_CasimirPowerSurjectiveSymmetric
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerLim
import Definitions.Def_ReciprocityTheory_Chebotarev_PrimeAsymp
import Theorems.Thm_ReciprocityTheory_Cheb_pa_cpow_eq
import Theorems.Thm_ReciprocityTheory_Cheb_pa_rpow_lt_one
import Theorems.Thm_ReciprocityTheory_Cheb_euler_exp_log
import Theorems.Thm_ReciprocityTheory_Cheb_summable_absNorm_rpow


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
    Real.exp (∑' q : Prm E, -Real.log (1 - ((Nrm q : ℕ) : ℝ) ^ (-s))) =
      ∑' a : NZIdeal E, ((Ideal.absNorm a.1 : ℕ) : ℝ) ^ (-s) := by
  have hs0 : (0 : ℝ) < s := by linarith
  set f : Ideal (𝓞 E) → ℂ := fun a => ((Ideal.absNorm a : ℕ) : ℂ) ^ (-(s : ℂ)) with hfdef
  have hf1 : f 1 = 1 := by simp [hfdef]
  have hmul : ∀ a b : Ideal (𝓞 E), f (a * b) = f a * f b := by
    intro a b
    simp only [hfdef, map_mul, Nat.cast_mul]
    exact Complex.natCast_mul_natCast_cpow _ _ _
  have hnorm : ∀ a : Ideal (𝓞 E), ‖f a‖ = ((Ideal.absNorm a : ℕ) : ℝ) ^ (-s) := by
    intro a
    simp only [hfdef]
    rw [pa_cpow_eq, Complex.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  have hsum : Summable (fun a : NZIdeal E => ‖f a.1‖) := by
    simp only [hnorm]
    exact summable_absNorm_rpow E hs
  have hlt : ∀ q : Prm E, ‖f q.asIdeal‖ < 1 := by
    intro q
    rw [hnorm]
    exact pa_rpow_lt_one q hs0
  have h := euler_exp_log f hf1 hmul hsum hlt
  apply Complex.ofReal_injective
  rw [Complex.ofReal_exp, Complex.ofReal_tsum, Complex.ofReal_tsum]
  have e1 : (∑' q : Prm E, (((-Real.log (1 - ((Nrm q : ℕ) : ℝ) ^ (-s))) : ℝ) : ℂ)) =
      ∑' q : Prm E, -Complex.log (1 - f q.asIdeal) := by
    refine tsum_congr fun q => ?_
    have hx := pa_rpow_lt_one q hs0
    rw [Complex.ofReal_neg, Complex.ofReal_log (by linarith), Complex.ofReal_sub, Complex.ofReal_one,
      ← pa_cpow_eq]
    rfl
  have e2 : (∑' a : NZIdeal E, ((((Ideal.absNorm a.1 : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ)) = ∑' a : NZIdeal E, f a.1 := by
    refine tsum_congr fun a => ?_
    rw [← pa_cpow_eq]
  rw [e1, e2]
  exact h
end ReciprocityTheory.Cheb
