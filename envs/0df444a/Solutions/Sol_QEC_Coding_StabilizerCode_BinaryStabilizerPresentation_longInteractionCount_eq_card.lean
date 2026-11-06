-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.longInteractionCount_eq_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:16:22.772484+00:00
-- url     : https://prove2.me/submissions/798af223-ccad-4b04-9a69-28054e27c9b7

import Definitions.Def_QEC_Coding_Stabilizer_FixedGeneratorInteraction
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Definitions.Def_QEC_Locality_OptimalTradeoff_Interaction

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
    (embedding : Locality.UnitSeparatedEmbedding2D ι) (threshold : ℝ) :
    P.longInteractionCount embedding threshold =
      (P.interactionsAtLengthAtLeast embedding threshold).card :=
  rfl
end QEC.Coding.StabilizerCode.BinaryStabilizerPresentation
