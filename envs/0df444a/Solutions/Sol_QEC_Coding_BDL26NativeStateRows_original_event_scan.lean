-- Prove2me | solution 1 for QEC.Coding.BDL26NativeStateRows.original_event_scan
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T01:56:16.645252+00:00
-- url     : https://prove2.me/submissions/1aebe02b-c796-4160-bb6b-968279572a0d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_VariableRelabeling
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeStateRows
import Theorems.Thm_QEC_Coding_BDL26NativeStateRows_original_cache_read
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_VariableRelabeling_original_firstBadFrom
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

section
namespace QEC.Coding.BDL26NativeStateRows
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
open scoped Classical
open QEC.Coding.ProbabilisticConstruction
private theorem original_points (S : OddScale) (n : ℕ) (J : Vertex (P S n) → Space)
    (r lambda : ℝ) (K : ℕ) (T : Samples (Vertex (P S n))) (m : ℕ) :
    (fun v => points S n
      (executeQ S n (encodeSamples S n T) (originalTrace S n J r lambda K T m)).value
        ((decode S n).symm v))=
      assignment (X := fun _ : Vertex (P S n) => Space) (asTable T) (counters (X := fun _ : Vertex (P S n) => Space) (eventSupport (P S n) J r)
        (eventBad (P S n) J r lambda K) (asTable T) m) := by
  funext v
  exact congrArg Prod.snd (original_cache_read S n J r lambda K T m v)
private theorem decidableFamily_unique {Ω I : Type*} (B : I → Set Ω)
    (first second : ∀ i, DecidablePred (· ∈ B i)) : first=second := by
  funext i z
  exact Subsingleton.elim _ _
end
end QEC.Coding.BDL26NativeStateRows
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeStateRows
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
open scoped Classical
open QEC.Coding.ProbabilisticConstruction
namespace QEC.Coding.BDL26NativeStateRows
theorem _root_.solution (S : OddScale) (n : ℕ) (J : Vertex (P S n) → Space)
    (r lambda : ℝ) (K : ℕ) (T : Samples (Vertex (P S n))) (m : ℕ)
    (L : List (Event (P S n) J r)) :
    firstBadFrom (localEvent
      (BDL26RandomPerturbation.VariableRelabeling.pulledSupport (P S n) J r (decode S n))
      (BDL26RandomPerturbation.VariableRelabeling.pulledBad (P S n) J r lambda K (decode S n))) L
      (points S n (executeQ S n (encodeSamples S n T)
        (originalTrace S n J r lambda K T m)).value)=
      firstBadFrom (localEvent (eventSupport (P S n) J r)
        (eventBad (P S n) J r lambda K)) L
        (assignment (X := fun _ : Vertex (P S n) => Space) (asTable T) (counters (X := fun _ : Vertex (P S n) => Space) (eventSupport (P S n) J r)
          (eventBad (P S n) J r lambda K) (asTable T) m)) := by
  have hscan := BDL26RandomPerturbation.VariableRelabeling.original_firstBadFrom
    (P S n) J r lambda K (decode S n) L
      (points S n (executeQ S n (encodeSamples S n T)
        (originalTrace S n J r lambda K T m)).value)
  have hd :
      (fun (e : Event (P S n) J r) (z : Vertex (P S n) → Space) =>
        Classical.propDecidable (z ∈ localEvent (X := fun _ : Vertex (P S n) => Space)
          (eventSupport (P S n) J r) (eventBad (P S n) J r lambda K) e)) =
        geometricGlobalBadDecidable (P S n) J r lambda K :=
    decidableFamily_unique _ _ _
  rw [hd] at hscan
  exact hscan.trans
      (congrArg (fun z : Vertex (P S n) → Space =>
        firstBadFrom (localEvent (eventSupport (P S n) J r)
          (eventBad (P S n) J r lambda K)) L z)
        (original_points S n J r lambda K T m))
end QEC.Coding.BDL26NativeStateRows
