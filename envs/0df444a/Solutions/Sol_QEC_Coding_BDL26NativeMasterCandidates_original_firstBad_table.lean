-- Prove2me | solution 1 for QEC.Coding.BDL26NativeMasterCandidates.original_firstBad_table
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:26:41.266351+00:00
-- url     : https://prove2.me/submissions/eae201f9-61fd-4b0a-85d1-7e8163bd57e6

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeSupportMetadata
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Mathlib.Data.List.Sublists
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeMasterCandidates
import Theorems.Thm_QEC_Coding_BDL26NativeMasterCandidates_original_firstBad

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
    (r lambda : ℝ) (K : ℕ) (T : BDL26NativeStateRows.Samples (Vertex (P S n))) (m : ℕ) :
    firstBadFrom (localEvent (eventSupport (P S n) J r) (eventBad (P S n) J r lambda K))
        (originalOrderedEvents S n J r)
        (assignment (BDL26NativeStateRows.asTable T)
          (counters (X:=fun _ : Vertex (P S n) => Space) (eventSupport (P S n) J r)
            (eventBad (P S n) J r lambda K) (BDL26NativeStateRows.asTable T) m))=
      firstBadFrom (localEvent (eventSupport (P S n) J r) (eventBad (P S n) J r lambda K))
        ((Finset.univ : Finset (Event (P S n) J r)).sort (eventPriorityLE (P S n) J r))
        (assignment (BDL26NativeStateRows.asTable T)
          (counters (X:=fun _ : Vertex (P S n) => Space) (eventSupport (P S n) J r)
            (eventBad (P S n) J r lambda K) (BDL26NativeStateRows.asTable T) m)) :=
  original_firstBad S n J r lambda K _
end QEC.Coding.BDL26NativeMasterCandidates
