-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_NormalGermIntegrallyClosed_vanish_of_mem_map_7d7b72ea45e9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:31:59.569551+00:00
-- url     : https://prove2.me/submissions/e99e2280-73b9-4bce-adfc-6fb12d266432

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalGermIntegrallyClosed
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StZariskiAnalyticNormality
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRueckertNullstellensatz
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalGermIntegrallyClosed
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_NormalGermIntegrallyClosed_toGerm_surjective_5df4007014f9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_NormalGermIntegrallyClosed_toGerm_eq_iff_6da30c5633ae

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial Topology Filter
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.NormalGermIntegrallyClosed
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.NormalGermIntegrallyClosed
theorem _root_.solution {σ : Type} [Fintype σ] {I : Ideal (MvPolynomial σ ℂ)} {w : σ → ℂ} {u : anFun w}
    (hu : toGerm w u ∈ I.map (polyGerm w)) :
    ∀ᶠ z in 𝓝[zeroSetIn I] w, (u : (σ → ℂ) → ℂ) z = 0 := by
  have key : ∀ x, x ∈ Submodule.span (holGerms w) (polyGerm w '' (I : Set (MvPolynomial σ ℂ))) →
      ∃ v : anFun w, toGerm w v = x ∧ ∀ᶠ z in 𝓝[zeroSetIn I] w, (v : (σ → ℂ) → ℂ) z = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨q, hq, rfl⟩ := hx
      exact ⟨⟨fun z => eval z q, analyticAt_eval_polynomial w q⟩, rfl,
        eventually_nhdsWithin_of_forall fun z hz => hz q hq⟩
    | zero => exact ⟨0, map_zero _, Eventually.of_forall fun z => by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨u, rfl, hu⟩ := hx
      obtain ⟨v, rfl, hv⟩ := hy
      exact ⟨u + v, map_add _ _ _, by filter_upwards [hu, hv] with z h1 h2; simp [h1, h2]⟩
    | smul c x _ hx =>
      obtain ⟨v, rfl, hv⟩ := hx
      obtain ⟨b, rfl⟩ := toGerm_surjective w c
      exact ⟨b * v, by rw [map_mul, smul_eq_mul], by filter_upwards [hv] with z h; simp [h]⟩
  obtain ⟨v, hv, hv0⟩ := key _ hu
  have he : (u : (σ → ℂ) → ℂ) =ᶠ[𝓝 w] v := toGerm_eq_iff.1 hv.symm
  filter_upwards [nhdsWithin_le_nhds he, hv0] with z h1 h2
  rw [h1, h2]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.NormalGermIntegrallyClosed
