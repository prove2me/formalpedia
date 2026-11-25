-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DualPointLineDegreeAlt_isMultiHomog_X_00c1ddf81f17
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:22:29.997119+00:00
-- url     : https://prove2.me/submissions/fa2e09c5-4733-4f24-a610-e116878ca485

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLineDegreeDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_IsArithVarBotDualBlocksUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsHorizontalOfDimOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ArithVarZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualPointLineDegree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 MvPolynomial Matrix NumberField
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.DualPointLineDegreeAlt
namespace GroundTheory.Heights₂.Heights.DualPointLineDegreeAlt
theorem _root_.solution {T : Type} [Fintype T] (t : T) :
    IsMultiHomog (X ⟨(), t⟩ : MRing (fun _ : Unit => T)) (fun _ => 1) := by
  classical
  intro m hm k
  obtain ⟨⟩ := k
  rw [support_X, Finset.mem_singleton] at hm
  subst hm
  rw [Finset.sum_eq_single t]
  · simp
  · intro c _ hc
    rw [Finsupp.single_apply, if_neg]
    intro h
    exact hc (sigma_mk_injective h).symm
  · simp
end GroundTheory.Heights₂.Heights.DualPointLineDegreeAlt
