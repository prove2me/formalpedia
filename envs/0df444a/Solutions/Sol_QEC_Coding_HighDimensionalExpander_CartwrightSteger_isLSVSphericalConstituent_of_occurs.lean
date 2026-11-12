-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.isLSVSphericalConstituent_of_occurs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:09:27.037377+00:00
-- url     : https://prove2.me/submissions/c00d855b-a9cc-42d3-9e31-ea21a152e897

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_PrefixHeckeCompatibility
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_QuotientL2
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_RamanujanCriterion
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_isUnitary_of_occursInLSVAutomorphicL2

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
    (hoccurs : OccursInLSVAutomorphicL2 P r level sigma)
    (hirreducible : Representation.IsIrreducible sigma)
    (hspherical : IsSpherical sigma) :
    IsLSVSphericalConstituent P r level sigma := by
  exact ⟨hoccurs, hirreducible,
    isUnitary_of_occursInLSVAutomorphicL2 P r level sigma hoccurs,
    hspherical⟩
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
