-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.rankThree_isLSVRamanujanQuotient_iff_tempered_constituents
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:13:08.700756+00:00
-- url     : https://prove2.me/submissions/7c4325f4-6327-4087-aaa9-cb85b7282ec4

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
            IsTempered sigma) :
    IsLSVRamanujanQuotient P .three level ↔
      ∀ (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
        (sigma : Representation ℂ
          (HeckeGroup (BaseField P) Rank.three.matrixRank) V),
        IsLSVInfiniteDimensionalSphericalConstituent
            P .three level sigma →
          IsTempered sigma :=
  hLSV05aPropositionOneFive
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
