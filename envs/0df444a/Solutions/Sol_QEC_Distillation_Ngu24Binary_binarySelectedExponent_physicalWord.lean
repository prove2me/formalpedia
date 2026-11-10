-- Prove2me | solution 1 for QEC.Distillation.Ngu24Binary.binarySelectedExponent_physicalWord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T12:07:59.925055+00:00
-- url     : https://prove2.me/submissions/640acbd1-592a-436e-b2ac-835ec0bcfb9f

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryTaggedEncoding
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryPhysicalCCZ
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_BinaryConversion
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryCubicBridge
import Theorems.Thm_QEC_Coding_f256SelectedCoordinates_ternary_identity


set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding Semantics Ngu24MultiplicativeCSS Ngu24MultiplicativeCCZ
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
open scoped BigOperators
variable {J : Type} [Fintype J] [DecidableEq J]
namespace QEC.Distillation.Ngu24Binary
theorem _root_.solution
    (u : TaggedThreeCopyRegisterLabel F256 J) :
    binarySelectedExponent (taggedPhysicalWordEmbedding J u) =
      f256RMFEpsi (taggedCubicPhaseExponent Finset.univ u) := by
  unfold binarySelectedExponent binarySelectedSites
  erw [Finset.sum_product]
  change (∑ j : J, ∑ q ∈ f256SelectedCoordinates,
    f256MFESigma (u (.first, j)) q * f256MFESigma (u (.second, j)) (f256MFEpi2 q) *
      f256MFESigma (u (.third, j)) (f256MFEpi3 q)) = _
  simp_rw [f256SelectedCoordinates_ternary_identity]
  rw [← map_sum]
  rfl
end QEC.Distillation.Ngu24Binary
