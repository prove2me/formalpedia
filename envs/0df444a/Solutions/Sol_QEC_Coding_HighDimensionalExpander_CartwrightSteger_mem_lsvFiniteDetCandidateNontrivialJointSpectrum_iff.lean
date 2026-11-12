-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.mem_lsvFiniteDetCandidateNontrivialJointSpectrum_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T18:43:45.394504+00:00
-- url     : https://prove2.me/submissions/c949934d-0efe-40e9-96bc-dc541c6a4c86

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
    (P : BasePrime) (r : Rank) (level : Nat)
    (eigenvalue : Fin (r.matrixRank - 1) → ℂ) :
    eigenvalue ∈ lsvFiniteDetCandidateNontrivialJointSpectrum P r level ↔
      ∃ vector,
        IsLSVJointEigenpair P r level eigenvalue vector ∧
          ¬ IsLSVFiniteDetCharacterVector P r level vector := by
  rfl
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
