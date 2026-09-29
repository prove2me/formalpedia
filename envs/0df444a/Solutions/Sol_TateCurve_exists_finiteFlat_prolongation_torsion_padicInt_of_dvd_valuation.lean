-- Prove2me | solution 1 for TateCurve.exists_finiteFlat_prolongation_torsion_padicInt_of_dvd_valuation
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/ea0881a1-25fe-5fc7-b8bf-91a23a6520ce

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_TateCurve_TateParameter
import Definitions.Def_TateCurve_TorsionParametrization
import Definitions.Def_FLTPrelim_GaloisRep
import Theorems.Thm_TateCurve_exists_finiteFlat_prolongation_torsion_padicInt_of_dvd_valuation_of_five_le
import Theorems.Thm_TateCurve_exists_finiteFlat_prolongation_torsion_padicInt_of_dvd_valuation_of_lt_five
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TateCurve_exists_finiteFlat_prolongation_torsion_padicInt_of_dvd_valuation
p2m_attr_erase "instance" "PadicInt.KummerCarrier.instFreeA PadicInt.KummerCarrier.instFiniteA"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero"

open scoped NNReal WeierstrassCurve.Affine
open WeierstrassCurve WeierstrassCurve.Affine.Point

theorem solution
    (p : ℕ) [Fact p.Prime] (qT : ℚ_[p]) (hqT0 : qT ≠ 0) (hqT1 : ‖qT‖₊ < 1)
    (hpr : (p : ℤ) ∣ Padic.valuation qT) :
    letI : DecidableEq (AlgebraicClosure ℚ_[p]) := Classical.decEq _
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra ℤ_[p] H),
      Module.Finite ℤ_[p] H ∧
      Module.Flat ℤ_[p] H ∧
      Coalgebra.IsCocomm ℤ_[p] H ∧
      ∃ e : WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]) ≃
          Submodule.torsionBy ℤ ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).Point p,
        (∀ f g, e (f * g) = e f + e g) ∧
        ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
          (f g : WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p])),
          (∀ h : H, g h = σ (f h)) → e g = σ • (e f) := by
  rcases Nat.lt_or_ge p 5 with hp5 | hp5
  · exact TateCurve.exists_finiteFlat_prolongation_torsion_padicInt_of_dvd_valuation_of_lt_five
      p hp5 qT hqT0 hqT1 hpr
  · exact TateCurve.exists_finiteFlat_prolongation_torsion_padicInt_of_dvd_valuation_of_five_le
      p hp5 qT hqT0 hqT1 hpr

end S_TateCurve_exists_finiteFlat_prolongation_torsion_padicInt_of_dvd_valuation
end P2MW
export P2MW.S_TateCurve_exists_finiteFlat_prolongation_torsion_padicInt_of_dvd_valuation (solution)
