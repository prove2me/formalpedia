-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.isLSVRamanujanQuotient_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:10:39.380392+00:00
-- url     : https://prove2.me/submissions/2a3dc72e-a1f8-4bdb-ae3e-e886f23f54e3

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_PrefixHeckeCompatibility
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_QuotientL2
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_RamanujanCriterion
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_isLSVFiniteDetCandidateSpectrumContainedInBuildingSpectrum_iff


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open QEC.Coding.HighDimensionalExpander.SphericalHecke
universe u
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat) :
    IsLSVRamanujanQuotient P r level ↔
      ∀ eigenvalue vector,
        IsLSVJointEigenpair P r level eigenvalue vector →
        ¬ IsLSVFiniteDetCharacterVector P r level vector →
        eigenvalue ∈ lsvUniversalBuildingJointSpectrum P r := by
  exact isLSVFiniteDetCandidateSpectrumContainedInBuildingSpectrum_iff
    P r level
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
