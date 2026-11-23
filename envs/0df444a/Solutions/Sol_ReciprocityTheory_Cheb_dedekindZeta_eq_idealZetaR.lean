-- Prove2me | solution 1 for ReciprocityTheory.Cheb.dedekindZeta_eq_idealZetaR
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:12:30.727747+00:00
-- url     : https://prove2.me/submissions/da87dbca-6b7a-49a6-96b1-0f548d7b5b45

import Definitions.Def_ReciprocityTheory_Chebotarev_NZIdeal
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
import Theorems.Thm_ReciprocityTheory_Cheb_idealZetaR_term_eq

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
    dedekindZeta E (s : ℂ) = ((idealZetaR E s : ℝ) : ℂ) := by
  unfold dedekindZeta LSeries idealZetaR
  rw [Complex.ofReal_tsum]
  exact tsum_congr fun n ↦ idealZetaR_term_eq E (zero_lt_one.trans hs) n
end ReciprocityTheory.Cheb
