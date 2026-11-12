-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.rankFour_isLSVRamanujanQuotient_iff_tempered_constituents
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:13:57.19648+00:00
-- url     : https://prove2.me/submissions/d605a0ff-da2a-4270-9f31-045eaf73bcf3

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
      IsLSVRamanujanQuotient P .four level ↔
        ∀ (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
          (sigma : Representation ℂ
            (HeckeGroup (BaseField P) Rank.four.matrixRank) V),
          IsLSVInfiniteDimensionalSphericalConstituent
              P .four level sigma →
            IsTempered sigma) :
    IsLSVRamanujanQuotient P .four level ↔
      ∀ (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
        (sigma : Representation ℂ
          (HeckeGroup (BaseField P) Rank.four.matrixRank) V),
        IsLSVInfiniteDimensionalSphericalConstituent
            P .four level sigma →
          IsTempered sigma :=
  hLSV05aPropositionOneFive
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
