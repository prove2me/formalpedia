-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_compAt_separates_7b711f540c86
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:22.25285+00:00
-- url     : https://prove2.me/submissions/192fb4bf-4a57-498e-8ece-a5b2771bd5b9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PPlaceMaps
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_compAt_tmul_635eb167447d
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_compAt_tmul_e1d8fccf6a3e
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.conj_conj



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.StrongApprox
open Matrix NumberField IsDedekindDomain TensorProduct ReciprocityTheory.ChartRestriction.G.SA
open GroundTheory.Heights₂.Heights.StrongApprox.PlaceMaps
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [Algebra F E]
namespace GroundTheory.Heights₂.Heights.StrongApprox.PlaceMaps
theorem _root_.solution (a b : AE F E) (h : ∀ v, compAt E v a = compAt E v b) : a = b := by
  let 𝒞 := Module.Free.chooseBasis F E
  have key : ∀ (v : HeightOneSpectrum (𝓞 F)) (x : AE F E) k,
      equivFinsuppOfBasisRight 𝒞 (compAt E v x) k =
        evalAt F v (equivFinsuppOfBasisRight 𝒞 x k) := by
    intro v x k
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      rw [compAt_tmul, equivFinsuppOfBasisRight_apply_tmul_apply,
        equivFinsuppOfBasisRight_apply_tmul_apply, map_smul]
    | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  apply (equivFinsuppOfBasisRight 𝒞).injective
  refine Finsupp.ext fun k => FiniteAdeleRing.ext _ fun w => ?_
  have hk := congrArg (fun z => equivFinsuppOfBasisRight 𝒞 z k) (h w)
  simp only [key] at hk
  exact hk
end GroundTheory.Heights₂.Heights.StrongApprox.PlaceMaps
