-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_germValue_polyToGerm_212cae8864c7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:31:06.838147+00:00
-- url     : https://prove2.me/submissions/d7af7989-d48d-41ea-b9fa-4eeafd7bc96c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_WeierstrassRemainderUnique
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAnalyticGermsNoetherian
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHolGermsDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_WeierstrassPolynomialRing

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
open Topology Filter Polynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {σ : Type} [Fintype σ] (p : (holGerms (0 : σ → ℂ))[X]) :
    germValue 0 (polyToGerm σ p) = (p.map (germValue 0)).eval 0 := by
  have h1 : (germValue (0 : Option σ → ℂ)).comp (germLift σ) = germValue 0 := by
    ext φ
    obtain ⟨f, -, hf⟩ := φ.2
    show Germ.value ((germLift σ φ : holGerms (0 : Option σ → ℂ)) : Germ (𝓝 (0 : Option σ → ℂ)) ℂ) =
      Germ.value (φ : Germ (𝓝 (0 : σ → ℂ)) ℂ)
    rw [germLift, germPull_coe _ _ _ φ f hf, ← hf]
    simp [lastProj]
    rfl
  rw [eval_map, polyToGerm, coe_eval₂RingHom, hom_eval₂, h1]
  rfl
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
