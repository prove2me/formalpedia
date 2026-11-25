-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_re_form_smul_e4e0127e2a9f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:53:04.486442+00:00
-- url     : https://prove2.me/submissions/4a44c149-9114-4b34-82b4-3d9503ca9222

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsUnfoldingTorus
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsTorusIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PArchLatticeDiscrete
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PVecAtNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnfoldingIntegral

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
open scoped ENNReal ComplexOrder
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
theorem _root_.solution (P : Matrix ι ι ℂ) (b : ℂ) (y : ι → ℂ) :
    (star (b • y) ⬝ᵥ (P *ᵥ (b • y))).re = (star y ⬝ᵥ (P *ᵥ y)).re * ‖b‖ ^ 2 := by
  have hb : star b * b = ((‖b‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_mul']
    norm_cast
  rw [star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
    ← mul_assoc, hb, Complex.re_ofReal_mul, mul_comm]
end GroundTheory.Heights₂.Heights.FiniteCovolume
