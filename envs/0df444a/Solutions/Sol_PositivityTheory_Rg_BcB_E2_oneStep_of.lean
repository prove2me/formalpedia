-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.E2.oneStep_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:20:55.396462+00:00
-- url     : https://prove2.me/submissions/04ea1e23-7fe5-4941-8858-71a34dd5e0b3

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_VecClose
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_EigenvalueSeparation_AlmostEverywhereEigen_OneStepOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal ComplexConjugate
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E2
open PositivityTheory.Rg.BcB.E1
namespace PositivityTheory.Rg.BcB.E2
theorem _root_.solution (h1 : Spec) (h2 : FData) (h3 : Desint) (h4 : HsSep) : OneStep := by
  classical
  intro X ι _ K _ _ _ J B _ _ _ _ R p a₀ C Φ g W hJ hp ha hC h1C hΦ hT hW hW' hWc hg hg' C₀ ε hε
  have hpos : 0 < ‖p a₀‖ := norm_pos_iff.2 ha
  obtain ⟨S, _, ν, _, χ, V, hS, hae⟩ := h1 K B R p (insert a₀ C₀) (min ε (‖p a₀‖ / 2)) hp (lt_min hε (half_pos hpos))
  have hne : ∀ᵐ s ∂ν, χ s a₀ ≠ 0 := hae.mono fun s hs e => by
    have := (hs a₀ (Finset.mem_insert_self _ _)).trans (min_le_right _ _)
    rw [e, zero_sub, norm_neg] at this
    linarith
  obtain ⟨F, hF⟩ := h2 X ι K J B R a₀ Φ g W S ν χ V hJ hΦ hT hS hne hW hW' hWc hg hg'
  have := h4 X ι
  have : SecondCountableTopology (X.Hs ι) := UniformSpace.secondCountable_of_separable _
  have : SecondCountableTopology (Lp ℂ 2 ν) :=
    (AddMonoidHomClass.isometry_of_norm (J.comp V) fun h => (hJ _).trans (hS.iso h)).isEmbedding.secondCountableTopology
  have := hC.to_subtype
  obtain ⟨s, hs, f, hf⟩ := h3 X ι C S ν F W (fun c : C => Φ c) (fun c s => χ s (c * a₀)) _ ⟨1, h1C⟩ _
    ⟨hF.cont, hF.inv, hF.ne, hF.wt, fun c => hF.eig c, hF.gint, hF.orth⟩ hW (fun c => hΦ c)
    (fun c => ⟨hS.meas _, _, hS.bdd _⟩) (by simpa using hne) (hae.and hne)
  exact ⟨χ s, f, fun c hc => (hs.1 c (Finset.mem_insert_of_mem hc)).trans (min_le_left _ _), hs.2, fun b => hS.bdd b s, hf⟩
end PositivityTheory.Rg.BcB.E2
