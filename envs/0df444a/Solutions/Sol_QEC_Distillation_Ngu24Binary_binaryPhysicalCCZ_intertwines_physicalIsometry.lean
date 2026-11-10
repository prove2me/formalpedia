-- Prove2me | solution 1 for QEC.Distillation.Ngu24Binary.binaryPhysicalCCZ_intertwines_physicalIsometry
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T12:13:49.339028+00:00
-- url     : https://prove2.me/submissions/1dc777a5-a1ab-415d-9390-e3dede0da999

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryTaggedEncoding
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryPhysicalCCZ
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_BinaryConversion
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryCubicBridge
import Theorems.Thm_QEC_Distillation_Ngu24Binary_binarySelectedExponent_physicalWord
import Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryPhysicalCCZ_apply_basis
import Theorems.Thm_QEC_Distillation_Ngu24Binary_taggedPhysicalIsometry_basis
import Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCCZ_taggedCubicPhysicalTransport_apply_basis


set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding Semantics Ngu24MultiplicativeCSS Ngu24MultiplicativeCCZ
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
open scoped BigOperators
variable {J : Type} [Fintype J] [DecidableEq J]
namespace QEC.Distillation.Ngu24Binary
theorem _root_.solution :
    (binaryPhysicalCCZ (J := J)).toLinearEquiv.toLinearMap.comp
        (taggedPhysicalIsometry J).toLinearMap =
      (taggedPhysicalIsometry J).toLinearMap.comp
        (taggedCubicPhysicalTransport (J := J) f256RMFEpsi).toLinearEquiv.toLinearMap := by
  apply (EuclideanSpace.basisFun (TaggedThreeCopyRegisterLabel F256 J) Complex).toBasis.ext
  intro u
  change binaryPhysicalCCZ (taggedPhysicalIsometry J (registerBasisKet u)) =
    taggedPhysicalIsometry J (taggedCubicPhysicalTransport f256RMFEpsi (registerBasisKet u))
  rw [taggedPhysicalIsometry_basis, binaryPhysicalCCZ_apply_basis,
    taggedCubicPhysicalTransport_apply_basis, map_smul, taggedPhysicalIsometry_basis]
  rw [binarySelectedExponent_physicalWord]
  rfl
end QEC.Distillation.Ngu24Binary
