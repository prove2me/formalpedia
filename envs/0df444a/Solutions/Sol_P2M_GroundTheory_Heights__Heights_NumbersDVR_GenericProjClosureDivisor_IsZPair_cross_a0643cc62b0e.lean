-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_IsZPair_cross_a0643cc62b0e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:21:59.209447+00:00
-- url     : https://prove2.me/submissions/854953e0-682d-4109-a068-35a6c7c9608e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsGenericProjClosureDivisor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsTwistedDualGensExpress
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Cartier
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericProjClosureDivisor
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_cross_mem_dae8c470757e

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
variable [∀ k, Fintype (ι k)]
omit [Algebra O Ω] [IsScalarTower O Ω Φ]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.GenericProjClosureDivisor
namespace IsZPair
theorem _root_.solution {a₀ a₀' : K → ℤ} {z : (Σ o, bundleIdx (bundleIdx ι M) M' o) → Φ}
    {f g f' g' : MRing (bundleIdx (bundleIdx ι M) M') O} (h : IsZPair a₀ a₀' z f g)
    (h' : IsZPair a₀ a₀' z f' g') : f * g' - f' * g ∈ pointIdeal O z := by
  obtain ⟨⟨bf, bg, hf, hg, hd⟩, hv⟩ := h
  obtain ⟨⟨bf', bg', hf', hg', hd'⟩, hv'⟩ := h'
  exact cross_mem hf hg hf' hg' (fun o => (congrFun hd o).trans (congrFun hd' o).symm) hv hv'
end IsZPair
end GroundTheory.Heights₂.Heights.NumbersDVR.GenericProjClosureDivisor
