-- Prove2me | solution 1 for ReciprocityTheory.Cheb.nonprime_term_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:13:29.772551+00:00
-- url     : https://prove2.me/submissions/b4da5c05-fc13-44be-a475-8d1ce78426cc

import Definitions.Def_ReciprocityTheory_Chebotarev_NZIdeal
import Definitions.Def_ReciprocityTheory_Chebotarev_CycTail
import Theorems.Thm_ReciprocityTheory_Cheb_primeBelow_prime
import Theorems.Thm_ReciprocityTheory_Cheb_primeBelow_sq_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open ReciprocityTheory ReciprocityTheory.Cheb
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.Cheb
theorem _root_.solution (q : Prm E) :
    (if (Nrm q).Prime then (0 : ℝ) else ((Nrm q : ℕ) : ℝ)⁻¹) ≤ 1 / ((primeBelow q : ℕ) : ℝ) ^ 2 := by
  split_ifs with h
  · positivity
  · have hq := primeBelow_sq_le q h
    have hp := (primeBelow_prime q).pos
    have hq' : ((primeBelow q : ℝ)) ^ 2 ≤ (Nrm q : ℝ) := by exact_mod_cast hq
    have hpos : (0 : ℝ) < (primeBelow q : ℝ) ^ 2 := by positivity
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le hpos hq'
end ReciprocityTheory.Cheb
