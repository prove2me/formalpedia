-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_map_eq_of_measurePreserving_coordinates_3ae251505cbd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:33:01.861264+00:00
-- url     : https://prove2.me/submissions/27225ec7-3cbf-4fa9-ba7e-db89a3c5bfcc

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DetSqEqOneOfPreservesBilin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentModulusHaar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open MeasureTheory Module
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
theorem _root_.solution {N V : Type*} [Group N] [TopologicalSpace N]
    [IsTopologicalGroup N] [LocallyCompactSpace N] [SecondCountableTopology N] [MeasurableSpace N]
    [BorelSpace N] [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] (lam : Measure V)
    [IsFiniteMeasureOnCompacts lam] [lam.IsOpenPosMeasure] (φ : V ≃ₜ N)
    (hL : ∀ n : N, MeasurePreserving (fun x => φ.symm (n * φ x)) lam lam)
    (c : N → N) (hC : MeasurePreserving (fun x => φ.symm (c (φ x))) lam lam)
    (μ : Measure N) [μ.IsHaarMeasure] : μ.map c = μ := by
  have hφ : Measurable φ := φ.continuous.measurable
  have key : ∀ T : V → V, MeasurePreserving T lam lam →
      (lam.map φ).map (φ ∘ T ∘ φ.symm) = lam.map φ := by
    intro T hT
    rw [Measure.map_map (hφ.comp (hT.measurable.comp φ.symm.continuous.measurable)) hφ]
    have : (φ ∘ T ∘ φ.symm) ∘ φ = φ ∘ T := by
      funext x
      simp
    rw [this, ← Measure.map_map hφ hT.measurable, hT.map_eq]
  have hinv : (lam.map φ).IsMulLeftInvariant := by
    refine ⟨fun n => ?_⟩
    have e : (fun x => n * x) = φ ∘ (fun x => φ.symm (n * φ x)) ∘ φ.symm := by
      funext x
      simp
    rw [e]
    exact key _ (hL n)
  have : IsFiniteMeasureOnCompacts (lam.map φ) := by
    refine ⟨fun K hK => ?_⟩
    have e := φ.toMeasurableEquiv.map_apply (μ := lam) K
    simp only [Homeomorph.toMeasurableEquiv_coe] at e
    rw [e]
    exact (φ.isCompact_preimage.2 hK).measure_lt_top
  have : (lam.map φ).IsOpenPosMeasure := φ.continuous.isOpenPosMeasure_map φ.surjective
  have : (lam.map φ).IsHaarMeasure := {}
  rw [Measure.isMulLeftInvariant_eq_smul μ (lam.map φ), Measure.map_smul]
  congr 1
  have e : c = φ ∘ (fun x => φ.symm (c (φ x))) ∘ φ.symm := by
    funext x
    simp
  rw [e]
  exact key _ hC
end GroundTheory.Heights₂.Heights.FiniteCovolume
