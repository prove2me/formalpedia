-- Prove2me | solution 1 for QuantumMaxCutEnergy.agm_product_value_scaling
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-01T14:54:35.943897+00:00
-- url     : https://prove2.me/submissions/20578078-94ac-4c45-96ee-9e6cbb3c1215

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
Numerical-only conversion for the rank-three product-estimation subproblem.
S denotes the classical Max-Cut SDP value. A separate analytic rounding
argument must prove 0.954*S ≤ OPT; a separate certified SDP solver must
compute a rational lower estimate L with additive error at most W/10000.
No random rounding, state preparation, or finite Gaussian sampler is needed
by this conversion. The algorithmic obligations remain separate.
-/

namespace AGMRoute

theorem scaled_sdp_value_bounds (O W S L : ℝ)
    (hstruct : (O + W) / 3 ≤ S)
    (hgap : (0.954 : ℝ) * S ≤ O)
    (hL0 : 0 ≤ L) (hLS : L ≤ S)
    (herror : S - L ≤ W / 10000) :
    0 ≤ (0.954 : ℝ) * L ∧
      (0.954 : ℝ) * L ≤ O ∧
      (0.953 : ℝ) * (O + W) / 3 ≤ (0.954 : ℝ) * L := by
  constructor
  · linarith
  constructor
  · linarith
  · linarith

/-- The exact-zero instance needs no division or exceptional convention. -/
theorem scaled_sdp_value_zero_weight (O S L : ℝ)
    (hstruct : O / 3 ≤ S)
    (hgap : (0.954 : ℝ) * S ≤ O)
    (hLS : L ≤ S) (herror : S - L ≤ 0) :
    L = S ∧ (0.954 : ℝ) * O / 3 ≤ (0.954 : ℝ) * L ∧
      (0.954 : ℝ) * L ≤ O := by
  constructor
  · linarith
  constructor <;> linarith

/-- Explicit loss accounting for the alternative sampled implementation. -/
theorem sampled_0954_to_0953 (O W E : ℝ) (hO : 0 ≤ O) (hW : 0 ≤ W)
    (hE : (0.999 * 0.954 : ℝ) * (O + W) / 3 - W / 100000 ≤ E) :
    (0.953 : ℝ) * (O + W) / 3 ≤ E := by
  linarith

#print axioms scaled_sdp_value_bounds
#print axioms scaled_sdp_value_zero_weight
#print axioms sampled_0954_to_0953

end AGMRoute

theorem solution (O W S L : ℝ)
    (hstruct : (O + W) / 3 ≤ S)
    (hgap : (0.954 : ℝ) * S ≤ O)
    (hL0 : 0 ≤ L) (hLS : L ≤ S)
    (herror : S - L ≤ W / 10000) :
    0 ≤ (0.954 : ℝ) * L ∧
      (0.954 : ℝ) * L ≤ O ∧
      (0.953 : ℝ) * (O + W) / 3 ≤ (0.954 : ℝ) * L := by
  exact AGMRoute.scaled_sdp_value_bounds O W S L hstruct hgap hL0 hLS herror
#print axioms solution
