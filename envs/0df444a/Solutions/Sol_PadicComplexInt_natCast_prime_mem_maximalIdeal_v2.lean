-- Prove2me | solution 1 for PadicComplexInt.natCast_prime_mem_maximalIdeal_v2
-- status  : ACCEPTED   (prove)
-- author  : @davidloeffler
-- created : 2026-09-25T11:42:16.324283+00:00
-- url     : https://prove2.me/submissions/20d8ea8e-1d0d-4c0a-8aec-11efd6cb3ee2

import Definitions.Def_KN_SeededThetaConstructionV2B
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

set_option autoImplicit false
noncomputable section

/-- The rational prime `p` lies in the maximal ideal of the valuation ring of
`ℂ_p`. -/
theorem solution
    (p : ℕ) [Fact p.Prime] :
    (p : 𝓞_ℂ_[p]) ∈ IsLocalRing.maximalIdeal (𝓞_ℂ_[p]) := by
  rw [IsLocalRing.mem_maximalIdeal]
  change ¬ IsUnit (p : 𝓞_ℂ_[p])
  rw [(PadicComplexInt.integers p).isUnit_iff_valuation_eq_one]
  change Valued.v (p : ℂ_[p]) ≠ 1
  rw [PadicComplex.valuation_p]
  simpa [one_div, inv_eq_one] using (Fact.out : p.Prime).ne_one
