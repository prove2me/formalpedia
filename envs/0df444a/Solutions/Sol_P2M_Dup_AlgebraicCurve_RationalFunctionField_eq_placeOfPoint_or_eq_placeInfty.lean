-- Prove2me | solution 1 for P2M.Dup.AlgebraicCurve.RationalFunctionField.eq_placeOfPoint_or_eq_placeInfty
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/6cfd4548-58da-5540-b323-33de1612c317

import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Theorems.Thm_P2M_Dup_AlgebraicCurve_RationalFunctionField_eq_ofHeightOneSpectrum_or_eq_placeInfty
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RationalFunctionField_eq_placeOfPoint_or_eq_placeInfty
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

p2m_open "Polynomial IsDedekindDomain AlgebraicCurve~RationalFunctionField.exists_eq_placeOfPoint P2MW.S_AlgebraicCurve_RationalFunctionField_eq_placeOfPoint_or_eq_placeInfty.AlgebraicCurve AlgebraicCurve.RationalFunctionField~exists_eq_placeOfPoint P2MW.S_AlgebraicCurve_RationalFunctionField_eq_placeOfPoint_or_eq_placeInfty.AlgebraicCurve.RationalFunctionField"

open scoped Polynomial

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ofHeightOneSpectrum RationalFunctionField.eq_ofHeightOneSpectrum_or_eq_placeInfty"
namespace RationalFunctionField
p2m_export "AlgebraicCurve.RationalFunctionField" "placeInfty heightOneSpectrumOfIrreducible heightOneSpectrumOfIrreducible_asIdeal exists_irreducible_span placeOfPoint placeOfPoint_eq_ofHeightOneSpectrum eq_ofHeightOneSpectrum_or_eq_placeInfty"
p2m_open "AlgebraicCurve.RationalFunctionField~exists_eq_placeOfPoint AlgebraicCurve~RationalFunctionField.exists_eq_placeOfPoint"

variable (K : Type*) [Field K]

theorem exists_eq_placeOfPoint [IsAlgClosed K] (w : HeightOneSpectrum K[X]) :
    ∃ a : K, Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w = placeOfPoint K a := by
  obtain ⟨p, hp, hwp⟩ := exists_irreducible_span K w

  have hdeg : p.degree ≠ 0 := by
    rw [IsAlgClosed.degree_eq_one_of_irreducible K hp]
    exact one_ne_zero
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root p hdeg
  refine ⟨a, ?_⟩

  have hassoc : Associated ((X : K[X]) - C a) p :=
    (irreducible_X_sub_C a).associated_of_dvd hp (dvd_iff_isRoot.mpr ha)
  have hideal : w = heightOneSpectrumOfIrreducible K (irreducible_X_sub_C a) :=
    HeightOneSpectrum.ext (by
      rw [hwp, heightOneSpectrumOfIrreducible_asIdeal]
      exact (Ideal.span_singleton_eq_span_singleton.mpr hassoc).symm)
  rw [hideal, placeOfPoint_eq_ofHeightOneSpectrum]

end AlgebraicCurve.RationalFunctionField

p2m_open "AlgebraicCurve~RationalFunctionField.exists_eq_placeOfPoint" in p2m_open "AlgebraicCurve.RationalFunctionField~exists_eq_placeOfPoint" in open _root_.P2MW.S_AlgebraicCurve_RationalFunctionField_eq_placeOfPoint_or_eq_placeInfty.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_RationalFunctionField_eq_placeOfPoint_or_eq_placeInfty.AlgebraicCurve.RationalFunctionField in
theorem solution (K : Type*) [Field K] [IsAlgClosed K] [DecidableEq (RatFunc K)] (v : Place K (RatFunc K)) : (∃ a : K, v = placeOfPoint K a) ∨ v = placeInfty K := by
  rcases AlgebraicCurve.RationalFunctionField.eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, hw⟩ | hw
  · obtain ⟨a, ha⟩ := exists_eq_placeOfPoint K w
    exact Or.inl ⟨a, hw.trans ha⟩
  · exact Or.inr hw

end S_AlgebraicCurve_RationalFunctionField_eq_placeOfPoint_or_eq_placeInfty
end P2MW
export P2MW.S_AlgebraicCurve_RationalFunctionField_eq_placeOfPoint_or_eq_placeInfty (solution)
