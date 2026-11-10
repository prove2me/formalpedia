-- Prove2me | solution 1 for QEC.Distillation.Ngu24MultiplicativeCCZ.taggedCubicPhaseAmplitude_eq_of_agree_on_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T11:37:02.863955+00:00
-- url     : https://prove2.me/submissions/929e7c63-6823-41aa-bed4-dccf61b660d5

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CCZIntertwining
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_CubicCSS
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CubicPhase
import Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCCZ_taggedCubicPhaseAmplitude_singleton
import Theorems.Thm_QEC_Distillation_taggedCoordinate_mem_coordinateSupport


set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24MultiplicativeCCZ
open Coding Semantics Ngu24MultiplicativeCSS
open scoped BigOperators
universe u
variable {F J I Logical : Type u} [Field F] [Fintype F] [Algebra (ZMod 2) F]
  [Fintype J] [DecidableEq J]
namespace QEC.Distillation.Ngu24MultiplicativeCCZ
theorem _root_.solution
    (f : F →ₗ[ZMod 2] ZMod 2) (site : J)
    (x y : TaggedThreeCopyRegisterLabel F J)
    (h : ∀ coordinate ∈ coordinateSupport site, x coordinate = y coordinate) :
    taggedCubicPhaseAmplitude f {site} x = taggedCubicPhaseAmplitude f {site} y := by
  rw [taggedCubicPhaseAmplitude_singleton, taggedCubicPhaseAmplitude_singleton,
    h (.first, site) (taggedCoordinate_mem_coordinateSupport .first site),
    h (.second, site) (taggedCoordinate_mem_coordinateSupport .second site),
    h (.third, site) (taggedCoordinate_mem_coordinateSupport .third site)]
end QEC.Distillation.Ngu24MultiplicativeCCZ
