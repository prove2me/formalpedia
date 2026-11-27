-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_NormalRiemannExtension_proof_248f3e6a6afa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:59:31.62227+00:00
-- url     : https://prove2.me/submissions/1429282b-d823-413d-bcb5-7bb3e3e21885

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalRiemannExtension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalRiemannExtensionLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalLocallyIrreducible
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalRiemannExtension

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
open MvPolynomial Topology
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace NormalRiemannExtension
theorem _root_.solution (hloc : NormalRiemannExtensionLocal.Statement)
    (hirr : NormalLocallyIrreducible.Statement) : NormalRiemannExtension.Statement := by
  intro σ _ I h U f hI hIc hh hU hf hb
  classical
  have hex : ∀ w ∈ zeroSetIn I ∩ U, ∃ V : Set (σ → ℂ), IsOpen V ∧ w ∈ V ∧ V ⊆ U ∧
      ∃ F : (σ → ℂ) → ℂ, DifferentiableOn ℂ F V ∧
        Set.EqOn F f ((zeroSetIn I ∩ V) \ {z | eval z h = 0}) := fun w hw =>
    hloc σ I h w U f hI hIc hh hw.1 (hU.mem_nhds hw.2) hf hb
  choose! V hVo hwV hVU F hF hFf using hex

  have hagree : ∀ w ∈ zeroSetIn I ∩ U, ∀ y ∈ zeroSetIn I ∩ U, y ∈ V w → F y y = F w y := by
    intro w hw y hy hyw
    have hWo : IsOpen (V y ∩ V w) := (hVo y hy).inter (hVo w hw)
    obtain ⟨B, -, hyB, hBW, -, hdense⟩ :=
      hirr σ I h y hI hIc hh hy.1 (V y ∩ V w) (hWo.mem_nhds ⟨hwV y hy, hyw⟩)
    set S := (zeroSetIn I ∩ B) \ {z | eval z h = 0}
    have hSW : insert y S ⊆ V y ∩ V w :=
      Set.insert_subset_iff.2 ⟨⟨hwV y hy, hyw⟩, fun z hz => hBW hz.1.2⟩
    have heq : Set.EqOn (F y) (F w) S := fun z hz => by
      have hzW := hBW hz.1.2
      rw [hFf y hy ⟨⟨hz.1.1, hzW.1⟩, hz.2⟩, hFf w hw ⟨⟨hz.1.1, hzW.2⟩, hz.2⟩]
    exact heq.of_subset_closure ((hF y hy).continuousOn.mono fun z hz => (hSW hz).1)
      ((hF w hw).continuousOn.mono fun z hz => (hSW hz).2) (Set.subset_insert y S)
      (Set.insert_subset_iff.2 ⟨hdense ⟨hy.1, hyB⟩, subset_closure⟩) (Set.mem_insert y S)
  refine ⟨fun z => if z ∈ zeroSetIn I ∩ U then F z z else f z, ?_, ?_⟩
  · intro w hw
    refine ⟨V w, hVo w hw, hwV w hw, F w, hF w hw, fun y hy => ?_⟩
    simp only [if_pos hy.1]
    exact hagree w hw y hy.1 hy.2
  · intro z hz
    simp only [if_pos hz.1]
    exact hFf z hz.1 ⟨⟨hz.1.1, hwV z hz.1⟩, hz.2⟩
end NormalRiemannExtension
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
