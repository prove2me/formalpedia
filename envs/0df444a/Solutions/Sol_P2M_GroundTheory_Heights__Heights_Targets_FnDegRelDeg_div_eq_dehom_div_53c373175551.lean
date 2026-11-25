-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_FnDegRelDeg_div_eq_dehom_div_53c373175551
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:29:27.602799+00:00
-- url     : https://prove2.me/submissions/957c46e1-056e-4794-bf22-ce125c8f2651

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsFnDegRelDeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PFnDegRelDeg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_chartProd_ne_zero_728a4ef52d77
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_cls_apply_7066b61ef8ff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_dehom_mul_of_isMultiHomog_db1b22d71340


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.FieldNumbers
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.Targets.FnDegRelDeg
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Targets.FnDegRelDeg
theorem _root_.solution (V : Ideal (MRing ι F)) [V.IsPrime] (i : ∀ k, ι k)
    (hi : ∀ k, (X ⟨k, i k⟩ : MRing ι F) ∉ V) {b : K → ℕ} {f g : MRing ι F}
    (hf : IsMultiHomog f b) (hg : IsMultiHomog g b) :
    algebraMap (MRing ι F ⧸ V) (FractionRing (MRing ι F ⧸ V)) (Ideal.Quotient.mk V f) /
        algebraMap (MRing ι F ⧸ V) (FractionRing (MRing ι F ⧸ V)) (Ideal.Quotient.mk V g) =
      IntNumPoint.dehom V i f / IntNumPoint.dehom V i g := by
  rw [← IntNumPoint.cls_apply, ← IntNumPoint.cls_apply,
    ← IntNumPoint.dehom_mul_of_isMultiHomog i hi hf, ← IntNumPoint.dehom_mul_of_isMultiHomog i hi hg,
    mul_div_mul_right _ _ (IntNumPoint.chartProd_ne_zero i hi b)]
end GroundTheory.Heights₂.Heights.Targets.FnDegRelDeg
