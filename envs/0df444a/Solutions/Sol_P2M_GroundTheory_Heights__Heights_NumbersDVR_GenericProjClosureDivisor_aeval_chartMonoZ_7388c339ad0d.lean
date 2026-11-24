-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_aeval_chartMonoZ_7388c339ad0d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:10.80053+00:00
-- url     : https://prove2.me/submissions/c03d2f89-9025-414e-9f80-9a7252658aa6

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
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
  {N M M' : ℕ} {E : Type} [AddCommGroup E] [Module Ω E]
  {Φ : Type} [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]
omit [Fintype K] [DecidableEq K] [Algebra O Ω] [IsScalarTower O Ω Φ]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.GenericProjClosureDivisor
theorem _root_.solution (y : (Σ k, ι k) → Ω) (e : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E) (t : Fin N → Φ) (c : ∀ k, ι k)
    (α : K → ℕ) [Fintype K] :
    aeval (pairProjCoord y e φ φ' t) (chartMonoZ O M M' c α) = algebraMap Ω Φ (∏ k, y ⟨k, c k⟩ ^ α k) := by
  rw [chartMonoZ, map_prod, map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_pow, map_pow, aeval_X]
  rfl
end GroundTheory.Heights₂.Heights.NumbersDVR.GenericProjClosureDivisor
