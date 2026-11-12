-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.mem_lsvNontrivialJointSpectrum_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:10:19.967873+00:00
-- url     : https://prove2.me/submissions/f57a0c79-3ae0-4f47-a34d-a994d798e942

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_PrefixHeckeCompatibility
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_QuotientL2
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_RamanujanCriterion
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_mem_lsvFiniteDetCandidateNontrivialJointSpectrum_iff


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open QEC.Coding.HighDimensionalExpander.SphericalHecke
universe u
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat)
    (eigenvalue : Fin (r.matrixRank - 1) → ℂ) :
    eigenvalue ∈ lsvNontrivialJointSpectrum P r level ↔
      ∃ vector,
        IsLSVJointEigenpair P r level eigenvalue vector ∧
          ¬ IsLSVFiniteDetCharacterVector P r level vector := by
  exact mem_lsvFiniteDetCandidateNontrivialJointSpectrum_iff
    P r level eigenvalue
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
