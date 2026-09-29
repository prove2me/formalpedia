-- Prove2me | solution 1 for WeierstrassCurve.inZeroComponentAt_of_isGoodPrimeFor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/943a9ba1-c43c-5596-b872-e0d4751910c7

import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_ZeroComponentAt
import Theorems.Thm_WeierstrassCurve_nonsingular_residue_of_isGoodPrimeFor
import Theorems.Thm_WeierstrassCurve_mem_valuationSubring_of_equation
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Algebra.Rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_inZeroComponentAt_of_isGoodPrimeFor

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem solution (W : WeierstrassCurve ℤ) {ℓ : ℕ} (hℓ : ℓ.Prime) (hgood : W.IsGoodPrimeFor ℓ) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ) (P : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) : W.InZeroComponentAt A P := by
  rcases P with _ | ⟨x, y, h⟩
  · exact Or.inl rfl
  · by_cases hx : x ∈ A
    · have hy : y ∈ A := WeierstrassCurve.mem_valuationSubring_of_equation W A h.left hx
      exact Or.inr ⟨x, y, h, rfl, Or.inr ⟨hx, hy,
        WeierstrassCurve.nonsingular_residue_of_isGoodPrimeFor W hℓ hgood A hA h.left hx hy⟩⟩
    · exact Or.inr ⟨x, y, h, rfl, Or.inl hx⟩

end S_WeierstrassCurve_inZeroComponentAt_of_isGoodPrimeFor
end P2MW
export P2MW.S_WeierstrassCurve_inZeroComponentAt_of_isGoodPrimeFor (solution)
