-- Prove2me | solution 1 for P2M_GlobalTheory_DetIdeal_pow_mem_pow__741349ce2029
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:31:23.734316+00:00
-- url     : https://prove2.me/submissions/03dfe089-4212-4166-9c77-431b9277f517

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FinrankEqOfInjectiveOfSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DetMulVolMulConj
import Theorems.Thm_GlobalTheory_DetIdeal_prod_mem_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.DetIdeal
variable {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] {r : ℕ}
namespace GlobalTheory.DetIdeal
theorem _root_.solution (c : FractionalIdeal R⁰ K) {t : K} (ht : t ∈ c) (n : ℕ) : t ^ n ∈ c ^ n := by
  simpa using prod_mem_pow c (Finset.range n) (fun _ => t) fun _ _ => ht
end GlobalTheory.DetIdeal
