-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_GradedFrameCharacterisation_mon_ne_zero_c2553a9ef5d0
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:47.540806+00:00
-- url     : https://prove2.me/submissions/989374d1-a6c4-4c41-93d9-1dbc981bb1c5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsTerBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueSat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinGradedFrameIff

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
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
universe u v w
open GroundTheory.Heights₂.Heights.NumbersDVR.GradedFrameCharacterisation
variable {o : Type u} [CommRing o] {Ω : Type v} [Field Ω] [Algebra o Ω] {K : Type} [Fintype K]
  {ι : K → Type} [∀ k, Fintype (ι k)] {y : (Σ k, ι k) → Ω} {N : ℕ} {E : Type w}
  [AddCommGroup E] [Module Ω E] {B : ChartBundle o (segreVec y) N E}
  {w : Module.Basis (Fin N) Ω E} {b : Fin N → K → ℤ}
omit [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.GradedFrameCharacterisation
theorem _root_.solution {c : ∀ k, ι k} (hc : segreVec y c ≠ 0) (a : K → ℤ) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.chartMon y c a ≠ 0 := by
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k =>
    (Finset.prod_ne_zero_iff.mp hc) k (Finset.mem_univ _)
  exact Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hy k)
end GroundTheory.Heights₂.Heights.NumbersDVR.GradedFrameCharacterisation
