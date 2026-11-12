-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.rankThree_isLSVRamanujanQuotient_of_tempered_constituents
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:13:27.841981+00:00
-- url     : https://prove2.me/submissions/3bd6030d-8473-4714-a8b1-7f3f80791107

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
    (P : BasePrime) (level : Nat)
    (hLSV05aPropositionOneFive :
      IsLSVRamanujanQuotient P .three level ↔
        ∀ (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
          (sigma : Representation ℂ
            (HeckeGroup (BaseField P) Rank.three.matrixRank) V),
          IsLSVInfiniteDimensionalSphericalConstituent
              P .three level sigma →
            IsTempered sigma)
    (htempered :
      ∀ (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
        (sigma : Representation ℂ
          (HeckeGroup (BaseField P) Rank.three.matrixRank) V),
        IsLSVInfiniteDimensionalSphericalConstituent
            P .three level sigma →
          IsTempered sigma) :
    IsLSVRamanujanQuotient P .three level :=
  hLSV05aPropositionOneFive.mpr htempered
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
