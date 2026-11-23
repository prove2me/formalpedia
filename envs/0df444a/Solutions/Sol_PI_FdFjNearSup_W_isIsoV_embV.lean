-- Prove2me | solution 1 for PI.FdFjNearSup.W.isIsoV_embV
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:33:37.730795+00:00
-- url     : https://prove2.me/submissions/ae676dea-dadc-44bb-96be-1aca93154d17

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicCoefficientSplitting
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_NearSupremumBounds_FdFjNearSupOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.FdFjNearSup PI.FdFjNearSup.W
open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex MeasureTheory
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace PI.FdFjNearSup.W
theorem _root_.solution {r : ℕ} (X : Data E r) {ξ : Fin r → E} (h : X.IsIso ξ) :
    X.IsIsoV (X.embV ξ) := by
  intro τ
  obtain ⟨-, hh, hne⟩ := h
  have key : hermC τ.1 X.Gm (X.embV ξ τ) (X.embV ξ τ) = τ.1 (herm X.Gm ξ ξ) := by
    simp only [hermC, herm, Data.embV, Data.emb, map_sum, map_mul, cc,
      IsCMField.complexEmbedding_complexConj]
  refine ⟨by rw [key, hh, map_zero], fun h0 => hne ?_⟩
  funext a
  have h1 := congrFun h0 a
  simp only [Data.embV, Data.emb, Pi.zero_apply, map_eq_zero] at h1
  simpa using h1
end PI.FdFjNearSup.W
