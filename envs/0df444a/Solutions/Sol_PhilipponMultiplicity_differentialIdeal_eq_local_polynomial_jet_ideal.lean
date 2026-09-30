-- Prove2me | solution 1 for PhilipponMultiplicity.differentialIdeal_eq_local_polynomial_jet_ideal
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-28T07:11:20.027697+00:00
-- url     : https://prove2.me/submissions/0e66c3d2-f0bf-41e3-b83c-cb4bd7c60625

import Theorems.Thm_PhilipponMultiplicity_differentialIdeal_le_local_polynomial_jet_ideal
import Theorems.Thm_PhilipponMultiplicity_local_polynomial_jet_ideal_le_differentialIdeal
import Definitions.Def_PhilipponMultiplicity_SectionFour
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Analytic.Polynomial
set_option autoImplicit false
open scoped BigOperators Topology
open PhilipponMultiplicity
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped ContDiff
open Filter MvPolynomial
noncomputable section

namespace PhilipponMultiplicity
private theorem completeSpace_of_isometric_ringEquiv
    {K F : Type*} [NontriviallyNormedField K] [NontriviallyNormedField F]
    [CompleteSpace F] (e : K ≃+* F) (he : Isometry e) : CompleteSpace K :=
  (he.isUniformInducing.completeSpace_congr e.surjective).mpr inferInstance

theorem IsPhilipponBaseField.completeSpace {K : Type*} [NontriviallyNormedField K]
    (hK : IsPhilipponBaseField K) : CompleteSpace K := by
  rcases hK with ⟨e, he⟩ | ⟨p, hp, h⟩
  · exact completeSpace_of_isometric_ringEquiv e he
  · letI : Fact p.Prime := ⟨hp⟩
    obtain ⟨e, he⟩ := h
    exact completeSpace_of_isometric_ringEquiv e he


end PhilipponMultiplicity

end

theorem solution
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G) (g : G.Point)
    (atlas : TranslationAtlas A g) (T : ℕ) (I : Ideal G.CoordinateRing)
    (hI : IsMultihomogeneousIdeal G.ambient I) :
    differentialIdeal A g T I = translatedIdeal G 0 (polynomialOperatorIdeal atlas T I) := by
  letI : CompleteSpace K := hK.completeSpace
  exact le_antisymm
    (differentialIdeal_le_local_polynomial_jet_ideal K G A g atlas T I)
    (local_polynomial_jet_ideal_le_differentialIdeal K hK G A g atlas T I hI)

