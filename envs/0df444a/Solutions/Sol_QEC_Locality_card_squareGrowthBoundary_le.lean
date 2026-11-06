-- Prove2me | solution 1 for QEC.Locality.card_squareGrowthBoundary_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:53:07.229889+00:00
-- url     : https://prove2.me/submissions/95908825-134a-419e-987b-93d4588852ba

import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Locality_OptimalTradeoff_PackingTiling
import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
import Theorems.Thm_QEC_Locality_card_longOutsideNeighborsOf_le_sum_counter
import Theorems.Thm_QEC_Locality_card_square_shell_le

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric
open QEC QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
attribute [local instance] QEC.Locality.instClassicalDecidableRecursive
namespace QEC.Locality
theorem _root_.solution
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (center : ℝ × ℝ)
    (outerRadius threshold : ℝ) (hthreshold : 1 ≤ threshold)
    (hdiameter : 1 ≤ 2 * outerRadius) :
    ((squareGrowthBoundary P embedding center outerRadius threshold).selected.card : ℝ) ≤
      48 * outerRadius * threshold +
        ((∑ q ∈ squareQubits embedding center (outerRadius - threshold),
          P.daiLiInteractionCounter embedding threshold q : Nat) : ℝ) := by
  let shell := squareQubits embedding center outerRadius \
    squareQubits embedding center (outerRadius - threshold)
  let outside := longOutsideNeighborsOf P embedding threshold
    (squareQubits embedding center (outerRadius - threshold))
  have hunionNat : (shell ∪ outside).card ≤ shell.card + outside.card :=
    Finset.card_union_le shell outside
  have houtside := card_longOutsideNeighborsOf_le_sum_counter P embedding threshold
    (squareQubits embedding center (outerRadius - threshold))
  calc
    _ ≤ (shell.card : ℝ) + (outside.card : ℝ) := by
      exact_mod_cast hunionNat
    _ ≤ 48 * outerRadius * threshold +
        ((∑ q ∈ squareQubits embedding center (outerRadius - threshold),
          P.daiLiInteractionCounter embedding threshold q : Nat) : ℝ) := by
      gcongr
      · exact card_square_shell_le embedding center outerRadius threshold
          hthreshold hdiameter
end QEC.Locality
