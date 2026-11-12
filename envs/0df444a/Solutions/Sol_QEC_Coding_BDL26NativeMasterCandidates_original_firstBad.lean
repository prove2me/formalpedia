-- Prove2me | solution 1 for QEC.Coding.BDL26NativeMasterCandidates.original_firstBad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T10:04:21.802201+00:00
-- url     : https://prove2.me/submissions/84836d61-52c0-4521-8315-9e4b7e688f64

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeSupportMetadata
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Mathlib.Data.List.Sublists
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeMasterCandidates
import Theorems.Thm_QEC_Coding_BDL26NativeMasterCandidates_original_ordered_exact

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeMasterCandidates
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
noncomputable section
open scoped Classical
namespace QEC.Coding.BDL26NativeMasterCandidates
theorem _root_.solution (S : OddScale) (n : ℕ) (J : Vertex (P S n) → Space)
    (r lambda : ℝ) (K : ℕ) (z : Vertex (P S n) → Space) :
    firstBadFrom (localEvent (eventSupport (P S n) J r) (eventBad (P S n) J r lambda K))
        (originalOrderedEvents S n J r) z=
      firstBadFrom (localEvent (eventSupport (P S n) J r) (eventBad (P S n) J r lambda K))
        ((Finset.univ : Finset (Event (P S n) J r)).sort (eventPriorityLE (P S n) J r)) z := by
  rw [original_ordered_exact]
end QEC.Coding.BDL26NativeMasterCandidates
