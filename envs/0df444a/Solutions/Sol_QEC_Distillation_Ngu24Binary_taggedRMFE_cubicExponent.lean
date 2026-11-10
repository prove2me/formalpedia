-- Prove2me | solution 1 for QEC.Distillation.Ngu24Binary.taggedRMFE_cubicExponent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T11:59:42.746352+00:00
-- url     : https://prove2.me/submissions/226e84d6-773d-4c8d-8212-417b4beaee2c

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryTaggedEncoding
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryPhysicalCCZ
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_BinaryConversion
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryCubicBridge
import Theorems.Thm_QEC_Coding_f256RMFE_ternary_reverse_mul


set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding Semantics Ngu24MultiplicativeCSS Ngu24MultiplicativeCCZ
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
open scoped BigOperators
variable {J : Type} [Fintype J] [DecidableEq J]
omit [DecidableEq J]
namespace QEC.Distillation.Ngu24Binary
theorem _root_.solution (u : TaggedThreeCopyRegisterLabel (ZMod 2) J) :
    f256RMFEpsi (taggedCubicPhaseExponent Finset.univ
      (logicalWordEmbedding (ThreeCopyTag × J) u)) =
      taggedCubicPhaseExponent Finset.univ u := by
  unfold taggedCubicPhaseExponent
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact f256RMFE_ternary_reverse_mul (u (.first, j)) (u (.second, j)) (u (.third, j))
end QEC.Distillation.Ngu24Binary
