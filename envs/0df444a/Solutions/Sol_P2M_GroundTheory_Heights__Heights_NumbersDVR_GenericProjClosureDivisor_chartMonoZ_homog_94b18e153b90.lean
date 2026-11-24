-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_chartMonoZ_homog_94b18e153b90
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:06.413801+00:00
-- url     : https://prove2.me/submissions/349fe5a6-2575-4517-bb15-53994245a39a

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
namespace GroundTheory.Heights₂.Heights.NumbersDVR.GenericProjClosureDivisor
theorem _root_.solution (c : ∀ k, ι k) (α : K → ℕ) :
    IsMultiHomog (chartMonoZ O M M' c α) (vdeg α) := by
  have h := IsWeightedHomogeneous.prod (R := O) Finset.univ
    (fun k => X (⟨some (some k), c k⟩ : Σ o, bundleIdx (bundleIdx ι M) M' o) ^ α k)
    (fun k => α k • blockWeight (bundleIdx (bundleIdx ι M) M') ⟨some (some k), c k⟩)
    (fun k _ => (isWeightedHomogeneous_X O _ _).pow (α k))
  have hw : vdeg α = ∑ k, α k • blockWeight (bundleIdx (bundleIdx ι M) M') ⟨some (some k), c k⟩ := by
    funext o
    rcases o with _ | _ | k <;> simp [vdeg, blockWeight, Finset.sum_apply, Pi.single_apply]
  rw [IsMultiHomog, chartMonoZ, hw]
  exact h
end GroundTheory.Heights₂.Heights.NumbersDVR.GenericProjClosureDivisor
