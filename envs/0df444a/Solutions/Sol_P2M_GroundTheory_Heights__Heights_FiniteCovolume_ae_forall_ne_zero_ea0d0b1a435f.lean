-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_ae_forall_ne_zero_ea0d0b1a435f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:13:33.236628+00:00
-- url     : https://prove2.me/submissions/0a435f50-ffd9-48c8-ab2e-d771149ee627

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsUnfoldingTorus
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsUnfoldAlongSubgroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsHaarParabolicCoordinates
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsStabilizerCovolume
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PScalingLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PArchLatticeDiscrete
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnfoldingTorus

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix MeasureTheory
open scoped ENNReal
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
theorem _root_.solution (κ : Type*) [Fintype κ] : ∀ᵐ b : κ → ℂ, ∀ w, b w ≠ 0 := by
  rw [ae_all_iff]
  intro w
  have h0 : volume ((fun b : κ → ℂ => b w) ⁻¹' {0}) = 0 :=
    Measure.pi_eval_preimage_null _ (measure_singleton 0)
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with b hb
  exact hb
end GroundTheory.Heights₂.Heights.FiniteCovolume
