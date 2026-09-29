-- Prove2me | solution 1 for ValuationSubring.charP_residueField_of_liesOverPrime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/a0f844cc-6441-5df7-836c-8ba233b59041

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_ModularCurve_ReductionOfPointsAgreesModL
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_FibreModel
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_AlgebraicCurve_CurveModelConstruction
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_charP_residueField_of_liesOverPrime
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve AlgebraicCurve IsLocalRing ModularCurve.IgusaScheme ModularCurve.CharPModel

open scoped TensorProduct
noncomputable section

theorem solution
    (ℓ : ℕ) [Fact ℓ.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime ℓ) : CharP (ResidueField ↥A) ℓ := by
  have hp : (ℓ : ℕ).Prime := Fact.out
  have hval : A.valuation (ℓ : AlgebraicClosure ℚ) < 1 := lt_of_le_of_ne hA.1 (fun h => hA.2 h.ge)
  have hcast : ((ℓ : ↥A) : AlgebraicClosure ℚ) = (ℓ : AlgebraicClosure ℚ) := by push_cast; ring
  have hnu : ¬ IsUnit (ℓ : ↥A) := by
    intro hu
    have := A.valuation_unit hu.unit
    rw [IsUnit.unit_spec, hcast] at this
    exact absurd this.ge hA.2
  have hmem : (ℓ : ↥A) ∈ maximalIdeal ↥A := (mem_maximalIdeal _).mpr hnu
  have hzero : (ℓ : ResidueField ↥A) = 0 := by
    rw [← map_natCast (residue ↥A)]; exact (residue_eq_zero_iff _).mpr hmem
  have hrc : ringChar (ResidueField ↥A) ∣ ℓ := (ringChar.spec _ ℓ).mp hzero
  have hrcℓ : ringChar (ResidueField ↥A) = ℓ :=
    (hp.eq_one_or_self_of_dvd _ hrc).resolve_left (CharP.ringChar_ne_one (R := ResidueField ↥A))
  exact hrcℓ ▸ ringChar.charP (ResidueField ↥A)

end
end S_ValuationSubring_charP_residueField_of_liesOverPrime
end P2MW
export P2MW.S_ValuationSubring_charP_residueField_of_liesOverPrime (solution)
