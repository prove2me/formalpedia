-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_HolGermPointIdealSpan_proof_312c77722db8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:57:39.935541+00:00
-- url     : https://prove2.me/submissions/2b2eb31a-1d0a-423b-bc59-bc59a10eed82

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StZariskiObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolGermPointIdealSpan
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHolGermPointIdealSpan
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_hadamard_decomposition_4d7972bd588d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_holGermValue_polyGerm_02f2c54c1f02


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
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace HolGermPointIdealSpan
theorem _root_.solution : HolGermPointIdealSpan.Statement := by
  intro σ _ w
  apply le_antisymm
  · rintro ⟨_, f, hf, rfl⟩ hφ
    have hfw : f w = 0 := hφ
    obtain ⟨g, hg, hfg⟩ := hadamard_decomposition hf
    have key : (⟨(f : Germ (𝓝 w) ℂ), f, hf, rfl⟩ : holGerms w) =
        ∑ i, polyGerm w (X i - C (w i)) * ⟨(g i : Germ (𝓝 w) ℂ), g i, hg i, rfl⟩ := by
      apply Subtype.ext
      change (f : Germ (𝓝 w) ℂ) = (holGerms w).subtype (∑ i, _)
      rw [map_sum]
      simp only [map_mul, Subring.coe_subtype]
      have hsum : ((fun z => ∑ i, (z i - w i) * g i z : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) =
          ∑ i, ((fun z : σ → ℂ => z i - w i : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) * (g i : Germ (𝓝 w) ℂ) := by
        change Germ.coeRingHom (𝓝 w) (fun z => ∑ i, (z i - w i) * g i z) = _
        rw [show (fun z => ∑ i, (z i - w i) * g i z : (σ → ℂ) → ℂ) =
            ∑ i, (fun z : σ → ℂ => z i - w i) * g i by
          funext z; simp [Finset.sum_apply], map_sum]
        rfl
      have hfe : (f : Germ (𝓝 w) ℂ) = ((fun z => ∑ i, (z i - w i) * g i z : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) :=
        Germ.coe_eq.mpr (hfg.mono fun z hz => by rw [hz, hfw, zero_add])
      rw [hfe, hsum]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      change _ = ((fun z : σ → ℂ => eval z (X i - C (w i)) : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ)
      simp
    rw [key]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    change holGermValue w (polyGerm w (X i - C (w i))) = 0
    rw [holGermValue_polyGerm]
    simp
end HolGermPointIdealSpan
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
