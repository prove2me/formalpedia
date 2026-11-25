-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_AnalyticGermComponents_isAnalyticNear_inter_zero_4847adeb363d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:31:55.008241+00:00
-- url     : https://prove2.me/submissions/6fd3eb17-c8c4-42a6-8777-e197fe95f386

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAnalyticGermComponents
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAnalyticGermsNoetherian
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAnalyticGermComponents

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
open Topology Filter
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.AnalyticGermComponents
variable {σ : Type} [Fintype σ]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.AnalyticGermComponents
theorem _root_.solution {X : Set (σ → ℂ)} {w : σ → ℂ} {f : (σ → ℂ) → ℂ}
    (hX : IsAnalyticNear X w) (hf : AnalyticAt ℂ f w) : IsAnalyticNear (X ∩ {z | f z = 0}) w := by
  obtain ⟨N, k, F, hN, hwN, hF, hXN⟩ := hX
  refine ⟨N ∩ {z | AnalyticAt ℂ f z}, k + 1, Fin.cons f F, hN.inter (isOpen_analyticAt ℂ f), ⟨hwN, hf⟩, ?_, ?_⟩
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · intro z hz
      simpa using hz.2
    · intro z hz
      simpa using hF j z hz.1
  · ext z
    have e := Set.ext_iff.1 hXN z
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq] at e ⊢
    simp only [Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ]
    constructor
    · rintro ⟨⟨hzX, hfz⟩, hzN, hza⟩
      exact ⟨⟨hzN, hza⟩, hfz, (e.1 ⟨hzX, hzN⟩).2⟩
    · rintro ⟨⟨hzN, hza⟩, hfz, hFz⟩
      exact ⟨⟨(e.2 ⟨hzN, hFz⟩).1, hfz⟩, hzN, hza⟩
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.AnalyticGermComponents
