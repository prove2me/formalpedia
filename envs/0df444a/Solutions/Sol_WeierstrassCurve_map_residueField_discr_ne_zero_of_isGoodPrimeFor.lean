-- Prove2me | solution 1 for WeierstrassCurve.map_residueField_discr_ne_zero_of_isGoodPrimeFor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/e418cade-7a16-5af6-834b-386ab0cbbd10

import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_valuation_intCast_eq_one_of_not_dvd
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Algebra.Rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_map_residueField_discr_ne_zero_of_isGoodPrimeFor

set_option autoImplicit false

open WeierstrassCurve

theorem solution (W : WeierstrassCurve ℤ) {ℓ : ℕ} (hℓ : ℓ.Prime) (hgood : W.IsGoodPrimeFor ℓ) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ) : (W.map (Int.castRingHom (IsLocalRing.ResidueField A))).Δ ≠ 0 := by
  have hℓ1 : A.valuation ((ℓ : ℕ) : AlgebraicClosure ℚ) < 1 := A.mem_nonunits_iff.mp hA
  have hv : A.valuation ((W.Δ : ℤ) : AlgebraicClosure ℚ) = 1 :=
    ValuationSubring.valuation_intCast_eq_one_of_not_dvd A hℓ hℓ1 hgood
  have hmem : ((W.Δ : ℤ) : AlgebraicClosure ℚ) ∈ A := intCast_mem A _
  have hunit : IsUnit (⟨_, hmem⟩ : A) := (A.valuation_eq_one_iff _).mpr hv
  have hcast : ((W.Δ : ℤ) : IsLocalRing.ResidueField A) = IsLocalRing.residue A ⟨_, hmem⟩ := by
    rw [show (⟨((W.Δ : ℤ) : AlgebraicClosure ℚ), hmem⟩ : A) = ((W.Δ : ℤ) : A) from
      Subtype.ext (by push_cast; rfl), map_intCast]
  rw [WeierstrassCurve.map_Δ, eq_intCast, hcast]
  exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hunit

end S_WeierstrassCurve_map_residueField_discr_ne_zero_of_isGoodPrimeFor
end P2MW
export P2MW.S_WeierstrassCurve_map_residueField_discr_ne_zero_of_isGoodPrimeFor (solution)
