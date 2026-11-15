-- Prove2me | solution 1 for PrimeLocal.norm_prime_le_norm_param_pow_of_prime_torsion
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-15T02:30:28.666206+00:00
-- url     : https://prove2.me/submissions/089b1523-57d9-4270-8ea8-de0758adfa7a

import Mathlib
import Theorems.Thm_PrimeLocal_exists_originParam_evalSeries_nthSeries_eq_zero
import Theorems.Thm_PrimeLocal_evalSeries_nthSeries_prime_ne_zero
import Theorems.Thm_WeierstrassCurve_exists_formalGroup_isComm_toPowerSeries_eq
import Definitions.Def_EllipticCurve_ZeroComponentAt
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_FLTPrelim_CofixedLine

set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open scoped WeierstrassCurve.Affine NNReal
universe u v

namespace PrimeLocal
theorem _root_.solution (p : ℕ) [Fact p.Prime] [DecidableEq ℂ_[p]] (D : WeierstrassCurve 𝓞_ℂ_[p]) (hΔ : D.Δ ≠ 0) (x y : ℂ_[p]) (h : (D.map (PadicComplexInt p).subtype).toAffine.Nonsingular x y) (hx : 1 < ‖x‖) (htor : p • (WeierstrassCurve.Affine.Point.some x y h) = 0) : ‖(p : ℂ_[p])‖ ≤ ‖x / y‖ ^ (p - 1) := by
  obtain ⟨F, hcomm, hF⟩ := D.exists_formalGroup_isComm_toPowerSeries_eq
  letI := hcomm
  obtain ⟨t, ht, ht0, ht1, hzero⟩ :=
    exists_originParam_evalSeries_nthSeries_eq_zero p D hΔ F hF x y h hx htor
  apply le_of_not_gt
  intro hsmall
  have hnorm : ‖(t : ℂ_[p])‖ = ‖x / y‖ := by rw [ht, neg_div, norm_neg]
  exact evalSeries_nthSeries_prime_ne_zero p F t ht0 ht1
    (by simpa only [hnorm] using hsmall) hzero
end PrimeLocal
