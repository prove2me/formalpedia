-- Prove2me | solution 1 for QEC.Distillation.Ngu24MultiplicativeCCZ.taggedCubicPhysicalTransport_apply_coset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T11:41:00.330881+00:00
-- url     : https://prove2.me/submissions/8415d39d-078e-4797-b5f5-898b53b22965

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CCZIntertwining
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_CubicCSS
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CubicPhase
import Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCCZ_taggedCubicPhysicalTransport_apply_basis
import Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCCZ_taggedCubicPhaseAmplitude_coset

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24MultiplicativeCCZ
open Coding Semantics Ngu24MultiplicativeCSS
open scoped BigOperators
universe u
variable {F J I Logical : Type u} [Field F] [Fintype F] [Algebra (ZMod 2) F]
  [Fintype J] [DecidableEq J]
variable [Fintype I] [Fintype Logical] [CharP F 2]
attribute [local instance] QEC.Distillation.Ngu24MultiplicativeCCZ._p2m_local_instance_bfada1b37a_179
namespace QEC.Distillation.Ngu24MultiplicativeCCZ
theorem _root_.solution (data : SourceInput F I Logical)
    (f : F →ₗ[ZMod 2] ZMod 2) (label : TaggedThreeCopyRegisterLabel F Logical) :
    taggedCubicPhysicalTransport f (taggedShortenedCosetKet data label) =
      taggedCubicPhaseAmplitude f Finset.univ label • taggedShortenedCosetKet data label := by
  unfold taggedShortenedCosetKet
  rw [map_smul, map_sum]
  simp_rw [taggedCubicPhysicalTransport_apply_basis, taggedCubicPhaseAmplitude_coset]
  rw [← Finset.smul_sum, smul_comm]
end QEC.Distillation.Ngu24MultiplicativeCCZ
