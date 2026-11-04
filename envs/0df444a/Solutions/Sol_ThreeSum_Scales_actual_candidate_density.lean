-- Prove2me | solution 1 for ThreeSum.Scales.actual_candidate_density
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:56:39.081831+00:00
-- url     : https://prove2.me/submissions/4dbfb948-9158-4a6d-ac95-c250660f9caa

import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_ThreeSum_Asymptotics
import Definitions.Def_Submission_ThreeSum_PrimeDensity
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Sqrt
import Definitions.Def_Submission_ThreeSum_Scales
import Theorems.Thm_ThreeSum_Scales_primeWindow_tendsto_atTop
import Theorems.Thm_ThreeSum_PrimeDensity_eventually_candidate_density


set_option autoImplicit false
open ThreeSum ThreeSum.Scales
open Filter Real
open scoped Topology
noncomputable section
namespace ThreeSum.Scales
theorem _root_.solution :
    ∀ᶠ n : ℕ in atTop,
      (primeWindow n : ℝ) / (4 * Real.log (primeWindow n)) ≤
        (PrimeDensity.candidates (primeWindow n)).card :=
  primeWindow_tendsto_atTop.eventually PrimeDensity.eventually_candidate_density
end ThreeSum.Scales
