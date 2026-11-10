-- Prove2me | solution 1 for QEC.Distillation.Ngu24Binary.taggedLogicalIsometry_intertwines_binaryLogicalCCZ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T12:09:51.451376+00:00
-- url     : https://prove2.me/submissions/5a72813e-28f9-4a2b-8797-6bd629b18614

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryTaggedEncoding
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryPhysicalCCZ
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_BinaryConversion
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryCubicBridge
import Theorems.Thm_QEC_Distillation_Ngu24Binary_taggedRMFE_cubicExponent
import Theorems.Thm_QEC_Distillation_Ngu24Binary_taggedLogicalIsometry_basis
import Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCCZ_taggedCubicPhaseTransport_apply_basis
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
    (taggedCubicPhaseTransport (J := J) f256RMFEpsi Finset.univ).toLinearEquiv.toLinearMap.comp
        (taggedLogicalIsometry J).toLinearMap =
      (taggedLogicalIsometry J).toLinearMap.comp (binaryLogicalCCZ (J := J)).toLinearEquiv.toLinearMap := by
  apply (EuclideanSpace.basisFun (TaggedThreeCopyRegisterLabel (ZMod 2) J) Complex).toBasis.ext
  intro u
  change taggedCubicPhaseTransport f256RMFEpsi Finset.univ
      (taggedLogicalIsometry J (registerBasisKet u)) =
    taggedLogicalIsometry J (taggedCubicPhysicalTransport (LinearMap.id : (ZMod 2) →ₗ[ZMod 2] ZMod 2)
      (registerBasisKet u))
  rw [taggedLogicalIsometry_basis, taggedCubicPhaseTransport_apply_basis,
    taggedCubicPhysicalTransport_apply_basis, map_smul, taggedLogicalIsometry_basis]
  unfold taggedCubicPhaseAmplitude
  rw [taggedRMFE_cubicExponent]
  rfl
end QEC.Distillation.Ngu24Binary
