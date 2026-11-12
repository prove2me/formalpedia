-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.not_isLSVTrivial_and_infiniteDimensionalSphericalConstituent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:10:07.691995+00:00
-- url     : https://prove2.me/submissions/a624fa8d-3e3f-4210-bbcb-f850a7d476b4

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
      (HeckeGroup (BaseField P) r.matrixRank) V) :
    ¬ (IsLSVTrivialSphericalConstituent P r level sigma ∧
      IsLSVInfiniteDimensionalSphericalConstituent P r level sigma) := by
  rintro ⟨⟨_, hfinite⟩, ⟨_, hinfinite⟩⟩
  exact hinfinite hfinite
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
