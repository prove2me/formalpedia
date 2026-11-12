-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.isLSVFiniteDetCandidateSpectrumContainedInBuildingSpectrum_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T18:44:06.396437+00:00
-- url     : https://prove2.me/submissions/75d46cc4-3939-4a83-9313-1c84ee618419

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_QuotientComplex
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_UniversalBuildingSpectrum
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_FiniteSpectrum

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped BigOperators
open QEC.Coding.HighDimensionalExpander.SphericalHecke
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat) :
    IsLSVFiniteDetCandidateSpectrumContainedInBuildingSpectrum P r level ↔
      ∀ eigenvalue vector,
        IsLSVJointEigenpair P r level eigenvalue vector →
        ¬ IsLSVFiniteDetCharacterVector P r level vector →
        eigenvalue ∈ lsvUniversalBuildingJointSpectrum P r := by
  constructor
  · intro h eigenvalue vector heigen hnontrivial
    exact h ⟨vector, heigen, hnontrivial⟩
  · rintro h eigenvalue ⟨vector, heigen, hnontrivial⟩
    exact h eigenvalue vector heigen hnontrivial
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
