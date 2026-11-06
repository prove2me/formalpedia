-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.longInteractionCount_anti_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:16:37.700775+00:00
-- url     : https://prove2.me/submissions/19128ade-bc23-4fee-b79c-4f5c26af6b6a

import Definitions.Def_QEC_Coding_Stabilizer_FixedGeneratorInteraction
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Definitions.Def_QEC_Locality_OptimalTradeoff_Interaction
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_interactionsAtLengthAtLeast_anti_mono

set_option autoImplicit false
noncomputable section
open scoped Classical
open QEC
open QEC.Coding
open QEC.Coding.StabilizerCode
open QEC.Coding.StabilizerCode.BinaryStabilizerPresentation
open PauliSymplectic
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
namespace QEC.Coding.StabilizerCode.BinaryStabilizerPresentation
theorem _root_.solution
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : Locality.UnitSeparatedEmbedding2D ι)
    {low high : ℝ} (hlowhigh : low ≤ high) :
    P.longInteractionCount embedding high ≤ P.longInteractionCount embedding low :=
  Finset.card_le_card (P.interactionsAtLengthAtLeast_anti_mono embedding hlowhigh)
end QEC.Coding.StabilizerCode.BinaryStabilizerPresentation
