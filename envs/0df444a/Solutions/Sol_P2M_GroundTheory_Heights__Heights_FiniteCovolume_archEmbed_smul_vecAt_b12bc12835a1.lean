-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_archEmbed_smul_vecAt_b12bc12835a1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:48:06.314072+00:00
-- url     : https://prove2.me/submissions/170a4b1f-9459-467c-8d2a-c28e3d42f189

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PScalingLaw
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_archSmul_apply_a816435a31d0
import Theorems.Thm_GroundTheory_Automorphic_unitaryGroupEquivMatrix_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
open scoped Pointwise ComplexOrder ENNReal
noncomputable section
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable [NumberField E]
attribute [local instance] archMulAction
variable [NumberField F] [IsTotallyReal F] [IsTotallyComplex E]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
theorem _root_.solution (h : HermitianForm F E W) (v : Basis ι E W) (γ : h.unitaryGroup)
    (x : W) : archEmbed h v γ • vecAt v x = vecAt v (γ • x) := by
  funext w i
  rw [archSmul_apply]
  have hm : (((archEmbed h v γ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) =
      (LinearMap.toMatrix v v ((γ : W ≃ₗ[E] W) : W →ₗ[E] W)).map w.embedding := by
    rw [← unitaryGroupEquivMatrix_apply]
    rfl
  rw [hm]
  change _ = w.embedding (v.repr (((γ : W ≃ₗ[E] W) : W →ₗ[E] W) x) i)
  rw [← LinearMap.toMatrix_mulVec_repr v v, RingHom.map_mulVec]
  rfl
end GroundTheory.Heights₂.Heights.FiniteCovolume
