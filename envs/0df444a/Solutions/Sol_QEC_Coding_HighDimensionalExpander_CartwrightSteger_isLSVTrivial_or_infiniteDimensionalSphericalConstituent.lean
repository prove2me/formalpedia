-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.isLSVTrivial_or_infiniteDimensionalSphericalConstituent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:09:39.363744+00:00
-- url     : https://prove2.me/submissions/4dac6b3c-f4c1-45fc-9a79-413a4dd405c1

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_PrefixHeckeCompatibility
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_QuotientL2
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_RamanujanCriterion

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open QEC.Coding.HighDimensionalExpander.SphericalHecke
universe u
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat)
    {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (sigma : Representation ℂ
      (HeckeGroup (BaseField P) r.matrixRank) V)
    (hconstituent : IsLSVSphericalConstituent P r level sigma) :
    IsLSVTrivialSphericalConstituent P r level sigma ∨
      IsLSVInfiniteDimensionalSphericalConstituent P r level sigma := by
  by_cases hfinite : Module.Finite ℂ V
  · exact Or.inl ⟨hconstituent, hfinite⟩
  · exact Or.inr ⟨hconstituent, hfinite⟩
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
