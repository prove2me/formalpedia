-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_aeval_eq_zero_of_mem_938035ac7e4d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:41.15255+00:00
-- url     : https://prove2.me/submissions/91eb21b0-3016-4252-a61f-c9ecb0e64d70

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsGenericProjClosureDivisor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsTwistedDualGensExpress
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Cartier
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericProjClosureDivisor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.GenericProjClosureDivisor
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {O : Type} [CommRing O] {Φ : Type} [Field Φ] [Algebra O Φ]
omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.GenericProjClosureDivisor
theorem _root_.solution {z : (Σ k, ι k) → Φ} {f : MRing ι O} (hf : f ∈ pointIdeal O z) :
    aeval z f = 0 := by
  have key : ((aeval (fun _ : K => (1 : Φ))).restrictScalars O).comp (pointConeMap O z) = aeval z := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [pointConeMap]
  have h := congrArg (fun ψ => ψ f) key
  simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply] at h
  rw [← h]
  have hf' : pointConeMap O z f = 0 := hf
  rw [hf', map_zero]
end GroundTheory.Heights₂.Heights.NumbersDVR.GenericProjClosureDivisor
